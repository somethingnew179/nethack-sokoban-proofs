import NetHack.Soko22Hazard87.AndIntroBlocks0375
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro94000 (p : Pattern) (ha : d310056 p = 1) (hb : d333419 p = 1) : d298018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39771 q = 1) (hb : d310056 q = 1) : d297581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39771, d297581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93745 q ha hb
    | true =>
      simp only [d39771, d297581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93748 q ha hb
  have h2 (q : Pattern) (ha : d39772 q = 1) (hb : d310056 q = 1) : d297582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39772, d297582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39772, d297582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310056 q = 1) (hb : d333400 q = 1) : d297999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333400, d297999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d333400, d297999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310056 q = 1) (hb : d333401 q = 1) : d298000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333401, d298000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333401, d298000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310056 q = 1) (hb : d333403 q = 1) : d298002 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333403, d298002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333403, d298002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93998 q ha hb
  have h6 (q : Pattern) (ha : d310056 q = 1) (hb : d333404 q = 1) : d298003 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333404, d298003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333404, d298003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d310056 q = 1) (hb : d333405 q = 1) : d298004 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333405, d298004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333405, d298004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d310056 q = 1) (hb : d333406 q = 1) : d298005 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333406, d298005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d333406, d298005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d310056 q = 1) (hb : d333407 q = 1) : d298006 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333407, d298006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333407, d298006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310056 q = 1) (hb : d333414 q = 1) : d298013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333414, d298013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333414, d298013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93999 q ha hb
  have h11 (q : Pattern) (ha : d310056 q = 1) (hb : d333415 q = 1) : d298014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333415, d298014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333415, d298014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d310056 q = 1) (hb : d333416 q = 1) : d298015 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333416, d298015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d333416, d298015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d310056 q = 1) (hb : d333417 q = 1) : d298016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333417, d298016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d333417, d298016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d310056 q = 1) (hb : d333418 q = 1) : d298017 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333418, d298017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d333418, d298017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d310056 q = 1) (hb : d333419 q = 1) : d298018 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333419, d298018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d333419, d298018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94001 (p : Pattern) (ha : d310056 p = 1) (hb : d333425 p = 1) : d298024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310056 q = 1) (hb : d333420 q = 1) : d298019 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333420, d298019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333420, d298019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94000 q ha hb
  have h2 (q : Pattern) (ha : d310056 q = 1) (hb : d333421 q = 1) : d298020 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333421, d298020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333421, d298020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310056 q = 1) (hb : d333422 q = 1) : d298021 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333422, d298021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333422, d298021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310056 q = 1) (hb : d333423 q = 1) : d298022 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333423, d298022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333423, d298022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310056 q = 1) (hb : d333424 q = 1) : d298023 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333424, d298023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333424, d298023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310056 q = 1) (hb : d333425 q = 1) : d298024 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333425, d298024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333425, d298024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94002 (p : Pattern) (ha : d310056 p = 1) (hb : d333431 p = 1) : d310731 p = 1 := by
  have h0 (q : Pattern) (ha : d171102 q = 1) (hb : d310056 q = 1) : d282120 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d282120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93981 q ha hb
    | true =>
      simp only [d171102, d282120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93985 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d279816 q = 1) (hb : d310056 q = 1) : d282147 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d279816, d282147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279816, d282147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93989 q ha hb
  have h3 (q : Pattern) (ha : d279817 q = 1) (hb : d310056 q = 1) : d282148 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d279817, d282148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279817, d282148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310056 q = 1) (hb : d333367 q = 1) : d310697 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333367, d310697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333367, d310697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93993 q ha hb
  have h5 (q : Pattern) (ha : d310056 q = 1) (hb : d333368 q = 1) : d310698 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333368, d310698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333368, d310698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310056 q = 1) (hb : d333369 q = 1) : d310699 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333369, d310699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d333369, d310699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d310056 q = 1) (hb : d333396 q = 1) : d310726 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333396, d310726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333396, d310726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93997 q ha hb
  have h8 (q : Pattern) (ha : d310056 q = 1) (hb : d333397 q = 1) : d310727 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333397, d310727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333397, d310727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d310056 q = 1) (hb : d333398 q = 1) : d310728 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333398, d310728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333398, d310728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310056 q = 1) (hb : d333399 q = 1) : d310729 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d333399, d310729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333399, d310729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d310056 q = 1) (hb : d333426 q = 1) : d298025 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333426, d298025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333426, d298025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94001 q ha hb
  have h12 (q : Pattern) (ha : d310056 q = 1) (hb : d333427 q = 1) : d298026 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333427, d298026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333427, d298026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d310056 q = 1) (hb : d333428 q = 1) : d298027 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333428, d298027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333428, d298027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d310056 q = 1) (hb : d333429 q = 1) : d298028 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d333429, d298028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333429, d298028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d310056 q = 1) (hb : d333430 q = 1) : d310730 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d333430, d310730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333430, d310730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d310056 q = 1) (hb : d333431 q = 1) : d310731 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d333431, d310731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d333431, d310731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro94003 (p : Pattern) (ha : d310056 p = 1) (hb : d333437 p = 1) : d310737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310056 q = 1) (hb : d333432 q = 1) : d310732 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d333432, d310732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94002 q ha hb
    | true =>
      simp only [d333432, d310732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310056 q = 1) (hb : d333433 q = 1) : d310733 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d333433, d310733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333433, d310733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310056 q = 1) (hb : d333434 q = 1) : d310734 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d333434, d310734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333434, d310734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310056 q = 1) (hb : d333435 q = 1) : d310735 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d333435, d310735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333435, d310735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310056 q = 1) (hb : d333436 q = 1) : d310736 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d333436, d310736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333436, d310736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310056 q = 1) (hb : d333437 q = 1) : d310737 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d333437, d310737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333437, d310737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94004 (p : Pattern) (ha : d310057 p = 1) (hb : d333443 p = 1) : d310743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310056 q = 1) (hb : d333438 q = 1) : d310738 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d333438, d310738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94003 q ha hb
    | true =>
      simp only [d333438, d310738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310056 q = 1) (hb : d333439 q = 1) : d310739 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d333439, d310739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333439, d310739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310056 q = 1) (hb : d333440 q = 1) : d310740 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d333440, d310740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333440, d310740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310056 q = 1) (hb : d333441 q = 1) : d310741 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d333441, d310741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333441, d310741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310056 q = 1) (hb : d333442 q = 1) : d310742 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d333442, d310742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333442, d310742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310057 q = 1) (hb : d333443 q = 1) : d310743 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310057, d333443, d310743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310057, d333443, d310743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro94005 (p : Pattern) (ha : d310057 p = 1) (hb : d333449 p = 1) : d310749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310057 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310057 q = 1) (hb : d333444 q = 1) : d310744 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d333444, d310744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94004 q ha hb
    | true =>
      simp only [d333444, d310744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310057 q = 1) (hb : d333445 q = 1) : d310745 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d333445, d310745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333445, d310745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310057 q = 1) (hb : d333446 q = 1) : d310746 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d333446, d310746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333446, d310746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310057 q = 1) (hb : d333447 q = 1) : d310747 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d333447, d310747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333447, d310747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310057 q = 1) (hb : d333448 q = 1) : d310748 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d333448, d310748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333448, d310748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310057 q = 1) (hb : d333449 q = 1) : d310749 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d333449, d310749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333449, d310749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94006 (p : Pattern) (ha : d310057 p = 1) (hb : d333455 p = 1) : d310755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310057 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310057 q = 1) (hb : d333450 q = 1) : d310750 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d333450, d310750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94005 q ha hb
    | true =>
      simp only [d333450, d310750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310057 q = 1) (hb : d333451 q = 1) : d310751 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d333451, d310751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333451, d310751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310057 q = 1) (hb : d333452 q = 1) : d310752 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d333452, d310752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333452, d310752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310057 q = 1) (hb : d333453 q = 1) : d310753 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d333453, d310753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333453, d310753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310057 q = 1) (hb : d333454 q = 1) : d310754 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d333454, d310754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333454, d310754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310057 q = 1) (hb : d333455 q = 1) : d310755 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d333455, d310755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333455, d310755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94007 (p : Pattern) (ha : d310057 p = 1) (hb : d333461 p = 1) : d310761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310057 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310057 q = 1) (hb : d333456 q = 1) : d310756 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d333456, d310756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94006 q ha hb
    | true =>
      simp only [d333456, d310756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310057 q = 1) (hb : d333457 q = 1) : d310757 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d333457, d310757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333457, d310757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310057 q = 1) (hb : d333458 q = 1) : d310758 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d333458, d310758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333458, d310758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310057 q = 1) (hb : d333459 q = 1) : d310759 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d333459, d310759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333459, d310759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310057 q = 1) (hb : d333460 q = 1) : d310760 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d333460, d310760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333460, d310760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310057 q = 1) (hb : d333461 q = 1) : d310761 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d333461, d310761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333461, d310761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94008 (p : Pattern) (ha : d310057 p = 1) (hb : d333467 p = 1) : d310767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310057 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310057 q = 1) (hb : d333462 q = 1) : d310762 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d333462, d310762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94007 q ha hb
    | true =>
      simp only [d333462, d310762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310057 q = 1) (hb : d333463 q = 1) : d310763 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d333463, d310763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333463, d310763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310057 q = 1) (hb : d333464 q = 1) : d310764 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d333464, d310764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333464, d310764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310057 q = 1) (hb : d333465 q = 1) : d310765 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d333465, d310765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333465, d310765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310057 q = 1) (hb : d333466 q = 1) : d310766 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d333466, d310766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333466, d310766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310057 q = 1) (hb : d333467 q = 1) : d310767 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d333467, d310767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333467, d310767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94009 (p : Pattern) (ha : d310057 p = 1) (hb : d333473 p = 1) : d310773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310057 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310057 q = 1) (hb : d333468 q = 1) : d310768 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d333468, d310768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94008 q ha hb
    | true =>
      simp only [d333468, d310768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310057 q = 1) (hb : d333469 q = 1) : d310769 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d333469, d310769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d333469, d310769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310057 q = 1) (hb : d333470 q = 1) : d310770 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d333470, d310770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333470, d310770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310057 q = 1) (hb : d333471 q = 1) : d310771 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d333471, d310771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333471, d310771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310057 q = 1) (hb : d333472 q = 1) : d310772 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d333472, d310772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333472, d310772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310057 q = 1) (hb : d333473 q = 1) : d310773 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d333473, d310773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333473, d310773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94010 (p : Pattern) (ha : d242768 p = 1) (hb : d310112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242748 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242662 q = 1) (hb : d310107 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242662, d310107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93811 q ha hb
    | true =>
      simp only [d242662, d310107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93812 q ha hb
  have h5 (q : Pattern) (ha : d242749 q = 1) (hb : d310108 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242749, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242749, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242765 q = 1) (hb : d310109 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242765, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242765, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242766 q = 1) (hb : d310110 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242766, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242766, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242767 q = 1) (hb : d310111 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242767, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242767, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242768 q = 1) (hb : d310112 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242768, d310112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242768, d310112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro94011 (p : Pattern) (ha : d242789 p = 1) (hb : d310122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242697 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242748 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242662 q = 1) (hb : d310107 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242662, d310107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93811 q ha hb
    | true =>
      simp only [d242662, d310107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93812 q ha hb
  have h4 (q : Pattern) (ha : d242749 q = 1) (hb : d310108 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242749, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242749, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242765 q = 1) (hb : d310109 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242765, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242765, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242766 q = 1) (hb : d310110 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242766, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242766, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242767 q = 1) (hb : d310111 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242767, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242767, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242781 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242672 q = 1) (hb : d310117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242672, d310117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93814 q ha hb
    | true =>
      simp only [d242672, d310117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93815 q ha hb
  have h13 (q : Pattern) (ha : d242782 q = 1) (hb : d310118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242782, d310118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242782, d310118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242785 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242786 q = 1) (hb : d310119 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242786, d310119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242786, d310119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242787 q = 1) (hb : d310120 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242787, d310120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242787, d310120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242788 q = 1) (hb : d310121 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242788, d310121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242788, d310121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242789 q = 1) (hb : d310122 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242789, d310122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242789, d310122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro94012 (p : Pattern) (ha : d242809 p = 1) (hb : d310673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242781 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242672 q = 1) (hb : d310117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242672, d310117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93814 q ha hb
    | true =>
      simp only [d242672, d310117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93815 q ha hb
  have h3 (q : Pattern) (ha : d242782 q = 1) (hb : d310118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242782, d310118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242782, d310118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242785 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242786 q = 1) (hb : d310119 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242786, d310119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242786, d310119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242807 q = 1) (hb : d310120 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242807, d310120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242807, d310120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242808 q = 1) (hb : d310121 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242808, d310121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242808, d310121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242809 q = 1) (hb : d310673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242809, d310673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242809, d310673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94013 (p : Pattern) (ha : d242930 p = 1) (hb : d310684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242905 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242910 q = 1) (hb : d310679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242910, d310679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93847 q ha hb
    | true =>
      simp only [d242910, d310679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93852 q ha hb
  have h3 (q : Pattern) (ha : d242911 q = 1) (hb : d310680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242911, d310680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242911, d310680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242926 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242927 q = 1) (hb : d310681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242927, d310681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242927, d310681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242928 q = 1) (hb : d310682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242928, d310682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242928, d310682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242929 q = 1) (hb : d310683 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242929, d310683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242929, d310683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242930 q = 1) (hb : d310684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242930, d310684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242930, d310684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94014 (p : Pattern) (ha : d242943 p = 1) (hb : d310690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242680 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242790 q = 1) (hb : d310123 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242790, d310123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94010 q ha hb
    | true =>
      simp only [d242790, d310123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94011 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242803 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242804 q = 1) (hb : d310124 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242804, d310124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242804, d310124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242805 q = 1) (hb : d310671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242805, d310671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242805, d310671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242806 q = 1) (hb : d310672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242806, d310672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242806, d310672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242810 q = 1) (hb : d310674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242810, d310674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242810, d310674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94012 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242812 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242813 q = 1) (hb : d310675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242813, d310675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242813, d310675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242814 q = 1) (hb : d310676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242814, d310676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242814, d310676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242815 q = 1) (hb : d310677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242815, d310677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242815, d310677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242816 q = 1) (hb : d310678 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242816, d310678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242816, d310678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242931 q = 1) (hb : d310685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242931, d310685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242931, d310685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94013 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242938 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242939 q = 1) (hb : d310686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242939, d310686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242939, d310686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242940 q = 1) (hb : d310687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242940, d310687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242940, d310687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242941 q = 1) (hb : d310688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242941, d310688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242941, d310688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242942 q = 1) (hb : d310689 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242942, d310689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242942, d310689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242943 q = 1) (hb : d310690 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242943, d310690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242943, d310690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro94015 (p : Pattern) (ha : d242949 p = 1) (hb : d310696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242944 q = 1) (hb : d310691 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242944, d310691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242944, d310691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94014 q ha hb
  have h2 (q : Pattern) (ha : d242945 q = 1) (hb : d310692 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242945, d310692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242945, d310692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242946 q = 1) (hb : d310693 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242946, d310693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242946, d310693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242947 q = 1) (hb : d310694 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242947, d310694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242947, d310694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242948 q = 1) (hb : d310695 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242948, d310695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242948, d310695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242949 q = 1) (hb : d310696 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242949, d310696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242949, d310696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94016 (p : Pattern) (ha : d243151 p = 1) (hb : d310384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243071 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243080 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243118 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243045 q = 1) (hb : d310379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d310379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93864 q ha hb
    | true =>
      simp only [d243045, d310379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93865 q ha hb
  have h5 (q : Pattern) (ha : d243119 q = 1) (hb : d310380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d243119, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243148 q = 1) (hb : d310381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243148, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d243149 q = 1) (hb : d310382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243149, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243150 q = 1) (hb : d310383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243150, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243151 q = 1) (hb : d310384 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243151, d310384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243151, d310384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro94017 (p : Pattern) (ha : d243172 p = 1) (hb : d310394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243045 q = 1) (hb : d310379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d310379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93864 q ha hb
    | true =>
      simp only [d243045, d310379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93865 q ha hb
  have h4 (q : Pattern) (ha : d243119 q = 1) (hb : d310380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243119, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243147 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243148 q = 1) (hb : d310381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243148, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243149 q = 1) (hb : d310382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243149, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243150 q = 1) (hb : d310383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243150, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243157 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d243162 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d243164 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d243055 q = 1) (hb : d310389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d310389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93867 q ha hb
    | true =>
      simp only [d243055, d310389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93868 q ha hb
  have h13 (q : Pattern) (ha : d243165 q = 1) (hb : d310390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d310390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d243165, d310390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243168 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243169 q = 1) (hb : d310391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d310391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243169, d310391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243170 q = 1) (hb : d310392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243170, d310392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d243170, d310392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243171 q = 1) (hb : d310393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243171, d310393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d243171, d310393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243172 q = 1) (hb : d310394 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243172, d310394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243172, d310394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro94018 (p : Pattern) (ha : d243192 p = 1) (hb : d310702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243164 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243055 q = 1) (hb : d310389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d310389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93867 q ha hb
    | true =>
      simp only [d243055, d310389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93868 q ha hb
  have h3 (q : Pattern) (ha : d243165 q = 1) (hb : d310390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d310390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243165, d310390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243168 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243169 q = 1) (hb : d310391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d310391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243169, d310391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243190 q = 1) (hb : d310392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243190, d310392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243190, d310392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243191 q = 1) (hb : d310393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243191, d310393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243191, d310393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243192 q = 1) (hb : d310702 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243192, d310702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243192, d310702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94019 (p : Pattern) (ha : d243320 p = 1) (hb : d310713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243289 q = 1) (hb : d310708 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243289, d310708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93903 q ha hb
    | true =>
      simp only [d243289, d310708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93909 q ha hb
  have h3 (q : Pattern) (ha : d243290 q = 1) (hb : d310709 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243290, d310709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243290, d310709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243316 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243317 q = 1) (hb : d310710 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243317, d310710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243317, d310710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243318 q = 1) (hb : d310711 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243318, d310711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243318, d310711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243319 q = 1) (hb : d310712 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243319, d310712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243319, d310712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243320 q = 1) (hb : d310713 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243320, d310713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243320, d310713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94020 (p : Pattern) (ha : d243333 p = 1) (hb : d310719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243063 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243173 q = 1) (hb : d310395 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243173, d310395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94016 q ha hb
    | true =>
      simp only [d243173, d310395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94017 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243187 q = 1) (hb : d310396 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243187, d310396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243187, d310396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243188 q = 1) (hb : d310700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243188, d310700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243188, d310700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243189 q = 1) (hb : d310701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243189, d310701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243189, d310701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243193 q = 1) (hb : d310703 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243193, d310703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243193, d310703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94018 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d243195 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d243196 q = 1) (hb : d310704 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243196, d310704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243196, d310704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d243197 q = 1) (hb : d310705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243197, d310705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243197, d310705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d243198 q = 1) (hb : d310706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243198, d310706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243198, d310706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d243199 q = 1) (hb : d310707 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243199, d310707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243199, d310707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243321 q = 1) (hb : d310714 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243321, d310714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243321, d310714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94019 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243328 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243329 q = 1) (hb : d310715 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243329, d310715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243329, d310715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243330 q = 1) (hb : d310716 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243330, d310716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243330, d310716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d243331 q = 1) (hb : d310717 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243331, d310717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243331, d310717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d243332 q = 1) (hb : d310718 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243332, d310718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243332, d310718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d243333 q = 1) (hb : d310719 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243333, d310719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243333, d310719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro94021 (p : Pattern) (ha : d243339 p = 1) (hb : d310725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243334 q = 1) (hb : d310720 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243334, d310720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243334, d310720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94020 q ha hb
  have h2 (q : Pattern) (ha : d243335 q = 1) (hb : d310721 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243335, d310721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243335, d310721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243336 q = 1) (hb : d310722 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243336, d310722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243336, d310722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243337 q = 1) (hb : d310723 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243337, d310723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243337, d310723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243338 q = 1) (hb : d310724 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243338, d310724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243338, d310724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243339 q = 1) (hb : d310725 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243339, d310725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243339, d310725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94022 (p : Pattern) (ha : d243516 p = 1) (hb : d297570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243423 q = 1) (hb : d297565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243423, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93921 q ha hb
    | true =>
      simp only [d243423, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93922 q ha hb
  have h5 (q : Pattern) (ha : d243478 q = 1) (hb : d297566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243478, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d243478, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243513 q = 1) (hb : d297567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243513, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243513, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d243514 q = 1) (hb : d297568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243514, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243514, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243515 q = 1) (hb : d297569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243515, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243515, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243516 q = 1) (hb : d297570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243516, d297570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243516, d297570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro94023 (p : Pattern) (ha : d243537 p = 1) (hb : d297580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243423 q = 1) (hb : d297565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243423, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93921 q ha hb
    | true =>
      simp only [d243423, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93922 q ha hb
  have h4 (q : Pattern) (ha : d243478 q = 1) (hb : d297566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243478, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243478, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243513 q = 1) (hb : d297567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243513, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243513, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243514 q = 1) (hb : d297568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243514, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243514, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243515 q = 1) (hb : d297569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243515, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243515, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243522 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d243527 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d243433 q = 1) (hb : d297575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243433, d297575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93924 q ha hb
    | true =>
      simp only [d243433, d297575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93925 q ha hb
  have h13 (q : Pattern) (ha : d243530 q = 1) (hb : d297576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243530, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d243530, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243534 q = 1) (hb : d297577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243534, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243534, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243535 q = 1) (hb : d297578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243535, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d243535, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243536 q = 1) (hb : d297579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243536, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d243536, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243537 q = 1) (hb : d297580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243537, d297580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243537, d297580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro94024 (p : Pattern) (ha : d243557 p = 1) (hb : d298001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243433 q = 1) (hb : d297575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243433, d297575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93924 q ha hb
    | true =>
      simp only [d243433, d297575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93925 q ha hb
  have h3 (q : Pattern) (ha : d243530 q = 1) (hb : d297576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243530, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243530, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243534 q = 1) (hb : d297577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243534, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243534, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243555 q = 1) (hb : d297578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243555, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243555, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243556 q = 1) (hb : d297579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243556, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243556, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243557 q = 1) (hb : d298001 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243557, d298001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243557, d298001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94025 (p : Pattern) (ha : d243667 p = 1) (hb : d298012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243631 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243636 q = 1) (hb : d298007 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243636, d298007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93960 q ha hb
    | true =>
      simp only [d243636, d298007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro93966 q ha hb
  have h3 (q : Pattern) (ha : d243637 q = 1) (hb : d298008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243637, d298008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243637, d298008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243663 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243664 q = 1) (hb : d298009 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243664, d298009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243664, d298009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243665 q = 1) (hb : d298010 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243665, d298010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243665, d298010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243666 q = 1) (hb : d298011 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243666, d298011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243666, d298011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243667 q = 1) (hb : d298012 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243667, d298012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243667, d298012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94026 (p : Pattern) (ha : d243680 p = 1) (hb : d298018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243441 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243538 q = 1) (hb : d297581 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243538, d297581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94022 q ha hb
    | true =>
      simp only [d243538, d297581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94023 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243551 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243552 q = 1) (hb : d297582 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243552, d297582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243552, d297582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243553 q = 1) (hb : d297999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243553, d297999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243553, d297999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243554 q = 1) (hb : d298000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243554, d298000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243554, d298000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243558 q = 1) (hb : d298002 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243558, d298002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243558, d298002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94024 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d243560 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d243561 q = 1) (hb : d298003 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243561, d298003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243561, d298003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d243562 q = 1) (hb : d298004 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243562, d298004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243562, d298004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d243563 q = 1) (hb : d298005 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243563, d298005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243563, d298005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d243564 q = 1) (hb : d298006 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243564, d298006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243564, d298006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243668 q = 1) (hb : d298013 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243668, d298013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243668, d298013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94025 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243675 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243676 q = 1) (hb : d298014 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243676, d298014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243676, d298014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243677 q = 1) (hb : d298015 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243677, d298015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243677, d298015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d243678 q = 1) (hb : d298016 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243678, d298016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243678, d298016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d243679 q = 1) (hb : d298017 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243679, d298017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243679, d298017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d243680 q = 1) (hb : d298018 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243680, d298018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243680, d298018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro94027 (p : Pattern) (ha : d243686 p = 1) (hb : d298024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243681 q = 1) (hb : d298019 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243681, d298019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243681, d298019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94026 q ha hb
  have h2 (q : Pattern) (ha : d243682 q = 1) (hb : d298020 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243682, d298020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243682, d298020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243683 q = 1) (hb : d298021 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243683, d298021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243683, d298021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243684 q = 1) (hb : d298022 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243684, d298022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243684, d298022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243685 q = 1) (hb : d298023 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243685, d298023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243685, d298023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243686 q = 1) (hb : d298024 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243686, d298024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243686, d298024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94028 (p : Pattern) (ha : d243692 p = 1) (hb : d310731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242306 q = 1) (hb : d282120 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242306, d282120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71967 q ha hb
    | true =>
      simp only [d242306, d282120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71973 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242581 q = 1) (hb : d282147 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242581, d282147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242581, d282147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71979 q ha hb
  have h3 (q : Pattern) (ha : d242582 q = 1) (hb : d282148 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242582, d282148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242582, d282148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242950 q = 1) (hb : d310697 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242950, d310697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242950, d310697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94015 q ha hb
  have h5 (q : Pattern) (ha : d242951 q = 1) (hb : d310698 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242951, d310698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242951, d310698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242952 q = 1) (hb : d310699 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d242952, d310699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242952, d310699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243340 q = 1) (hb : d310726 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243340, d310726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243340, d310726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94021 q ha hb
  have h8 (q : Pattern) (ha : d243341 q = 1) (hb : d310727 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243341, d310727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243341, d310727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243342 q = 1) (hb : d310728 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243342, d310728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243342, d310728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243343 q = 1) (hb : d310729 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243343, d310729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243343, d310729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243687 q = 1) (hb : d298025 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243687, d298025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243687, d298025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94027 q ha hb
  have h12 (q : Pattern) (ha : d243688 q = 1) (hb : d298026 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243688, d298026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243688, d298026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243689 q = 1) (hb : d298027 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243689, d298027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243689, d298027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243690 q = 1) (hb : d298028 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243690, d298028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243690, d298028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243691 q = 1) (hb : d310730 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d243691, d310730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243691, d310730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243692 q = 1) (hb : d310731 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d243692, d310731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243692, d310731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro94029 (p : Pattern) (ha : d243698 p = 1) (hb : d310737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243693 q = 1) (hb : d310732 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d243693, d310732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94028 q ha hb
    | true =>
      simp only [d243693, d310732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243694 q = 1) (hb : d310733 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d243694, d310733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243694, d310733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243695 q = 1) (hb : d310734 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d243695, d310734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243695, d310734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243696 q = 1) (hb : d310735 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d243696, d310735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243696, d310735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243697 q = 1) (hb : d310736 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d243697, d310736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243697, d310736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243698 q = 1) (hb : d310737 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d243698, d310737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243698, d310737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94030 (p : Pattern) (ha : d243704 p = 1) (hb : d310743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243699 q = 1) (hb : d310738 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d243699, d310738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94029 q ha hb
    | true =>
      simp only [d243699, d310738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243700 q = 1) (hb : d310739 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d243700, d310739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243700, d310739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243701 q = 1) (hb : d310740 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d243701, d310740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243701, d310740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243702 q = 1) (hb : d310741 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d243702, d310741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243702, d310741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243703 q = 1) (hb : d310742 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d243703, d310742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243703, d310742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243704 q = 1) (hb : d310743 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d243704, d310743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243704, d310743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94031 (p : Pattern) (ha : d243710 p = 1) (hb : d310749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243705 q = 1) (hb : d310744 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d243705, d310744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94030 q ha hb
    | true =>
      simp only [d243705, d310744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243706 q = 1) (hb : d310745 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d243706, d310745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243706, d310745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243707 q = 1) (hb : d310746 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d243707, d310746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243707, d310746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243708 q = 1) (hb : d310747 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d243708, d310747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243708, d310747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243709 q = 1) (hb : d310748 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d243709, d310748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243709, d310748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243710 q = 1) (hb : d310749 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d243710, d310749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243710, d310749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94032 (p : Pattern) (ha : d243716 p = 1) (hb : d310755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243711 q = 1) (hb : d310750 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d243711, d310750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94031 q ha hb
    | true =>
      simp only [d243711, d310750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243712 q = 1) (hb : d310751 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d243712, d310751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243712, d310751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243713 q = 1) (hb : d310752 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d243713, d310752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243713, d310752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243714 q = 1) (hb : d310753 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d243714, d310753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243714, d310753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243715 q = 1) (hb : d310754 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d243715, d310754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243715, d310754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243716 q = 1) (hb : d310755 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d243716, d310755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243716, d310755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94033 (p : Pattern) (ha : d243722 p = 1) (hb : d310761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243717 q = 1) (hb : d310756 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d243717, d310756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94032 q ha hb
    | true =>
      simp only [d243717, d310756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243718 q = 1) (hb : d310757 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d243718, d310757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243718, d310757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243719 q = 1) (hb : d310758 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d243719, d310758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243719, d310758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243720 q = 1) (hb : d310759 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d243720, d310759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243720, d310759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243721 q = 1) (hb : d310760 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d243721, d310760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243721, d310760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243722 q = 1) (hb : d310761 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d243722, d310761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243722, d310761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94034 (p : Pattern) (ha : d243728 p = 1) (hb : d310767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243723 q = 1) (hb : d310762 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d243723, d310762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94033 q ha hb
    | true =>
      simp only [d243723, d310762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243724 q = 1) (hb : d310763 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d243724, d310763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243724, d310763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243725 q = 1) (hb : d310764 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d243725, d310764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243725, d310764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243726 q = 1) (hb : d310765 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d243726, d310765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243726, d310765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243727 q = 1) (hb : d310766 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d243727, d310766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243727, d310766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243728 q = 1) (hb : d310767 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d243728, d310767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243728, d310767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94035 (p : Pattern) (ha : d243734 p = 1) (hb : d310773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243729 q = 1) (hb : d310768 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d243729, d310768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94034 q ha hb
    | true =>
      simp only [d243729, d310768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243730 q = 1) (hb : d310769 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d243730, d310769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243730, d310769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243731 q = 1) (hb : d310770 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d243731, d310770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243731, d310770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243732 q = 1) (hb : d310771 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d243732, d310771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243732, d310771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243733 q = 1) (hb : d310772 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d243733, d310772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243733, d310772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243734 q = 1) (hb : d310773 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d243734, d310773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243734, d310773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro94036 (p : Pattern) (ha : d245512 p = 1) (hb : d310112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d310107 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245508 q = 1) (hb : d310108 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245508, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245509 q = 1) (hb : d310109 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245509, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245510 q = 1) (hb : d310110 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245510, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245511 q = 1) (hb : d310111 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245511, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245512 q = 1) (hb : d310112 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245512, d310112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245512, d310112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro94037 (p : Pattern) (ha : d245517 p = 1) (hb : d310122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310107 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245508 q = 1) (hb : d310108 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245508, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245509 q = 1) (hb : d310109 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245509, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245510 q = 1) (hb : d310110 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245510, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245511 q = 1) (hb : d310111 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245511, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31902 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31907 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d310117 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245513 q = 1) (hb : d310118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d310118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245513, d310118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245514 q = 1) (hb : d310119 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d310119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245514, d310119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245515 q = 1) (hb : d310120 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245515, d310120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245515, d310120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245516 q = 1) (hb : d310121 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245516, d310121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245516, d310121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245517 q = 1) (hb : d310122 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245517, d310122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245517, d310122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro94038 (p : Pattern) (ha : d245524 p = 1) (hb : d310673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245513 q = 1) (hb : d310118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d310118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245513, d310118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245514 q = 1) (hb : d310119 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d310119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245514, d310119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245522 q = 1) (hb : d310120 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245522, d310120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245522, d310120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245523 q = 1) (hb : d310121 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245523, d310121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245523, d310121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245524 q = 1) (hb : d310673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245524, d310673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245524, d310673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94039 (p : Pattern) (ha : d245534 p = 1) (hb : d310684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310679 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245530 q = 1) (hb : d310680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245530, d310680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245530, d310680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32109 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245531 q = 1) (hb : d310681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245531, d310681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245531, d310681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245532 q = 1) (hb : d310682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245532, d310682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245532, d310682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245533 q = 1) (hb : d310683 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245533, d310683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245533, d310683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245534 q = 1) (hb : d310684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245534, d310684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245534, d310684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94040 (p : Pattern) (ha : d245540 p = 1) (hb : d310690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31718 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245518 q = 1) (hb : d310123 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245518, d310123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94036 q ha hb
    | true =>
      simp only [d245518, d310123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94037 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245519 q = 1) (hb : d310124 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245519, d310124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245519, d310124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245520 q = 1) (hb : d310671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245520, d310671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245520, d310671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245521 q = 1) (hb : d310672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245521, d310672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245521, d310672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245525 q = 1) (hb : d310674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245525, d310674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245525, d310674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94038 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31943 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245526 q = 1) (hb : d310675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245526, d310675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245526, d310675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245527 q = 1) (hb : d310676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245527, d310676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245527, d310676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245528 q = 1) (hb : d310677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245528, d310677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245528, d310677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245529 q = 1) (hb : d310678 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245529, d310678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245529, d310678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245535 q = 1) (hb : d310685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245535, d310685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245535, d310685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94039 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32125 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245536 q = 1) (hb : d310686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245536, d310686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245536, d310686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245537 q = 1) (hb : d310687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245537, d310687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245537, d310687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245538 q = 1) (hb : d310688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245538, d310688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245538, d310688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245539 q = 1) (hb : d310689 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245539, d310689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245539, d310689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245540 q = 1) (hb : d310690 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245540, d310690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245540, d310690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro94041 (p : Pattern) (ha : d245546 p = 1) (hb : d310696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245541 q = 1) (hb : d310691 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245541, d310691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245541, d310691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94040 q ha hb
  have h2 (q : Pattern) (ha : d245542 q = 1) (hb : d310692 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245542, d310692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245542, d310692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245543 q = 1) (hb : d310693 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245543, d310693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245543, d310693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245544 q = 1) (hb : d310694 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245544, d310694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245544, d310694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245545 q = 1) (hb : d310695 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245545, d310695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245545, d310695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245546 q = 1) (hb : d310696 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245546, d310696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245546, d310696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94042 (p : Pattern) (ha : d245554 p = 1) (hb : d310384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d310379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245550 q = 1) (hb : d310380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245550, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245551 q = 1) (hb : d310381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245551, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245552 q = 1) (hb : d310382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245552, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245553 q = 1) (hb : d310383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245553, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245554 q = 1) (hb : d310384 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245554, d310384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245554, d310384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro94043 (p : Pattern) (ha : d245559 p = 1) (hb : d310394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310379 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245550 q = 1) (hb : d310380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245550, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245551 q = 1) (hb : d310381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245551, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245552 q = 1) (hb : d310382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245552, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245553 q = 1) (hb : d310383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245553, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d310389 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245555 q = 1) (hb : d310390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d310390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245555, d310390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245556 q = 1) (hb : d310391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d310391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245556, d310391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245557 q = 1) (hb : d310392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245557, d310392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245557, d310392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245558 q = 1) (hb : d310393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245558, d310393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245558, d310393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245559 q = 1) (hb : d310394 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245559, d310394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245559, d310394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro94044 (p : Pattern) (ha : d245566 p = 1) (hb : d310702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310389 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245555 q = 1) (hb : d310390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d310390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245555, d310390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245556 q = 1) (hb : d310391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d310391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245556, d310391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245564 q = 1) (hb : d310392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245564, d310392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245564, d310392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245565 q = 1) (hb : d310393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245565, d310393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245565, d310393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245566 q = 1) (hb : d310702 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245566, d310702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245566, d310702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94045 (p : Pattern) (ha : d245576 p = 1) (hb : d310713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310708 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245572 q = 1) (hb : d310709 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245572, d310709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245572, d310709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32655 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245573 q = 1) (hb : d310710 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245573, d310710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245573, d310710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245574 q = 1) (hb : d310711 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245574, d310711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245574, d310711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245575 q = 1) (hb : d310712 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245575, d310712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245575, d310712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245576 q = 1) (hb : d310713 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245576, d310713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245576, d310713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94046 (p : Pattern) (ha : d245582 p = 1) (hb : d310719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245560 q = 1) (hb : d310395 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245560, d310395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94042 q ha hb
    | true =>
      simp only [d245560, d310395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94043 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245561 q = 1) (hb : d310396 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245561, d310396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245561, d310396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245562 q = 1) (hb : d310700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245562, d310700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245562, d310700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245563 q = 1) (hb : d310701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245563, d310701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245563, d310701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245567 q = 1) (hb : d310703 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245567, d310703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245567, d310703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94044 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32482 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245568 q = 1) (hb : d310704 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245568, d310704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245568, d310704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245569 q = 1) (hb : d310705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245569, d310705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245569, d310705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245570 q = 1) (hb : d310706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245570, d310706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245570, d310706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245571 q = 1) (hb : d310707 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245571, d310707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245571, d310707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245577 q = 1) (hb : d310714 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245577, d310714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245577, d310714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94045 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32671 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245578 q = 1) (hb : d310715 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245578, d310715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245578, d310715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245579 q = 1) (hb : d310716 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245579, d310716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245579, d310716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245580 q = 1) (hb : d310717 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245580, d310717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245580, d310717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245581 q = 1) (hb : d310718 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245581, d310718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245581, d310718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245582 q = 1) (hb : d310719 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245582, d310719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245582, d310719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro94047 (p : Pattern) (ha : d245588 p = 1) (hb : d310725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245583 q = 1) (hb : d310720 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245583, d310720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245583, d310720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94046 q ha hb
  have h2 (q : Pattern) (ha : d245584 q = 1) (hb : d310721 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245584, d310721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245584, d310721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245585 q = 1) (hb : d310722 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245585, d310722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245585, d310722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245586 q = 1) (hb : d310723 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245586, d310723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245586, d310723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245587 q = 1) (hb : d310724 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245587, d310724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245587, d310724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245588 q = 1) (hb : d310725 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245588, d310725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245588, d310725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94048 (p : Pattern) (ha : d245597 p = 1) (hb : d297570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d297565 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245593 q = 1) (hb : d297566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245593, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245593, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245594 q = 1) (hb : d297567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245594, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245594, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245595 q = 1) (hb : d297568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245595, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245595, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245596 q = 1) (hb : d297569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245596, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245596, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245597 q = 1) (hb : d297570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245597, d297570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245597, d297570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro94049 (p : Pattern) (ha : d245602 p = 1) (hb : d297580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d297565 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245593 q = 1) (hb : d297566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245593, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245593, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245594 q = 1) (hb : d297567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245594, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245594, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245595 q = 1) (hb : d297568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245595, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245595, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245596 q = 1) (hb : d297569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245596, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245596, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32945 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32950 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d297575 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245598 q = 1) (hb : d297576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245598, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245598, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245599 q = 1) (hb : d297577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245599, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245599, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245600 q = 1) (hb : d297578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245600, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245600, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245601 q = 1) (hb : d297579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245601, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245601, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245602 q = 1) (hb : d297580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245602, d297580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245602, d297580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro94050 (p : Pattern) (ha : d245609 p = 1) (hb : d298001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245598 q = 1) (hb : d297576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245598, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245598, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245599 q = 1) (hb : d297577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245599, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245599, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245607 q = 1) (hb : d297578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245607, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245607, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245608 q = 1) (hb : d297579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245608, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245608, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245609 q = 1) (hb : d298001 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245609, d298001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245609, d298001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94051 (p : Pattern) (ha : d245619 p = 1) (hb : d298012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33057 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298007 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245615 q = 1) (hb : d298008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245615, d298008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245615, d298008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245616 q = 1) (hb : d298009 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245616, d298009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245616, d298009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245617 q = 1) (hb : d298010 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245617, d298010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245617, d298010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245618 q = 1) (hb : d298011 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245618, d298011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245618, d298011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245619 q = 1) (hb : d298012 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245619, d298012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245619, d298012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94052 (p : Pattern) (ha : d245625 p = 1) (hb : d298018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32784 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245603 q = 1) (hb : d297581 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245603, d297581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94048 q ha hb
    | true =>
      simp only [d245603, d297581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94049 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245604 q = 1) (hb : d297582 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245604, d297582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245604, d297582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245605 q = 1) (hb : d297999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245605, d297999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245605, d297999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245606 q = 1) (hb : d298000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245606, d298000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245606, d298000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245610 q = 1) (hb : d298002 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245610, d298002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245610, d298002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94050 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32986 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245611 q = 1) (hb : d298003 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245611, d298003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245611, d298003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245612 q = 1) (hb : d298004 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245612, d298004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245612, d298004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245613 q = 1) (hb : d298005 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245613, d298005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245613, d298005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245614 q = 1) (hb : d298006 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245614, d298006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245614, d298006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245620 q = 1) (hb : d298013 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245620, d298013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245620, d298013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94051 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245621 q = 1) (hb : d298014 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245621, d298014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245621, d298014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245622 q = 1) (hb : d298015 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245622, d298015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245622, d298015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245623 q = 1) (hb : d298016 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245623, d298016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245623, d298016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245624 q = 1) (hb : d298017 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245624, d298017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245624, d298017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245625 q = 1) (hb : d298018 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245625, d298018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245625, d298018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro94053 (p : Pattern) (ha : d245631 p = 1) (hb : d298024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245626 q = 1) (hb : d298019 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245626, d298019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245626, d298019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94052 q ha hb
  have h2 (q : Pattern) (ha : d245627 q = 1) (hb : d298020 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245627, d298020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245627, d298020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245628 q = 1) (hb : d298021 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245628, d298021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245628, d298021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245629 q = 1) (hb : d298022 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245629, d298022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245629, d298022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245630 q = 1) (hb : d298023 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245630, d298023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245630, d298023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245631 q = 1) (hb : d298024 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245631, d298024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245631, d298024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94054 (p : Pattern) (ha : d245637 p = 1) (hb : d310731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d245466 q = 1) (hb : d282120 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245466, d282120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72011 q ha hb
    | true =>
      simp only [d245466, d282120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72017 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245506 q = 1) (hb : d282147 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245506, d282147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245506, d282147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72023 q ha hb
  have h3 (q : Pattern) (ha : d245507 q = 1) (hb : d282148 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245507, d282148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245507, d282148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245547 q = 1) (hb : d310697 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245547, d310697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245547, d310697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94041 q ha hb
  have h5 (q : Pattern) (ha : d245548 q = 1) (hb : d310698 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245548, d310698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245548, d310698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245549 q = 1) (hb : d310699 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245549, d310699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245549, d310699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245589 q = 1) (hb : d310726 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245589, d310726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245589, d310726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94047 q ha hb
  have h8 (q : Pattern) (ha : d245590 q = 1) (hb : d310727 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245590, d310727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245590, d310727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245591 q = 1) (hb : d310728 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245591, d310728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245591, d310728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245592 q = 1) (hb : d310729 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245592, d310729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245592, d310729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245632 q = 1) (hb : d298025 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245632, d298025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245632, d298025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94053 q ha hb
  have h12 (q : Pattern) (ha : d245633 q = 1) (hb : d298026 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245633, d298026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245633, d298026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245634 q = 1) (hb : d298027 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245634, d298027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245634, d298027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245635 q = 1) (hb : d298028 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245635, d298028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245635, d298028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245636 q = 1) (hb : d310730 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245636, d310730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245636, d310730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245637 q = 1) (hb : d310731 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245637, d310731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245637, d310731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro94055 (p : Pattern) (ha : d245643 p = 1) (hb : d310737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245638 q = 1) (hb : d310732 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245638, d310732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94054 q ha hb
    | true =>
      simp only [d245638, d310732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245639 q = 1) (hb : d310733 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245639, d310733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245639, d310733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245640 q = 1) (hb : d310734 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245640, d310734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245640, d310734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245641 q = 1) (hb : d310735 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245641, d310735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245641, d310735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245642 q = 1) (hb : d310736 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245642, d310736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245642, d310736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245643 q = 1) (hb : d310737 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245643, d310737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245643, d310737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94056 (p : Pattern) (ha : d245649 p = 1) (hb : d310743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245644 q = 1) (hb : d310738 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245644, d310738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94055 q ha hb
    | true =>
      simp only [d245644, d310738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245645 q = 1) (hb : d310739 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245645, d310739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245645, d310739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245646 q = 1) (hb : d310740 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245646, d310740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245646, d310740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245647 q = 1) (hb : d310741 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245647, d310741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245647, d310741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245648 q = 1) (hb : d310742 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245648, d310742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245648, d310742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245649 q = 1) (hb : d310743 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245649, d310743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245649, d310743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94057 (p : Pattern) (ha : d245655 p = 1) (hb : d310749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245650 q = 1) (hb : d310744 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245650, d310744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94056 q ha hb
    | true =>
      simp only [d245650, d310744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245651 q = 1) (hb : d310745 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245651, d310745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245651, d310745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245652 q = 1) (hb : d310746 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245652, d310746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245652, d310746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245653 q = 1) (hb : d310747 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245653, d310747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245653, d310747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245654 q = 1) (hb : d310748 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245654, d310748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245654, d310748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245655 q = 1) (hb : d310749 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245655, d310749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245655, d310749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94058 (p : Pattern) (ha : d245661 p = 1) (hb : d310755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245656 q = 1) (hb : d310750 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245656, d310750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94057 q ha hb
    | true =>
      simp only [d245656, d310750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245657 q = 1) (hb : d310751 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245657, d310751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245657, d310751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245658 q = 1) (hb : d310752 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245658, d310752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245658, d310752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245659 q = 1) (hb : d310753 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245659, d310753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245659, d310753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245660 q = 1) (hb : d310754 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245660, d310754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245660, d310754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245661 q = 1) (hb : d310755 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245661, d310755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245661, d310755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94059 (p : Pattern) (ha : d245667 p = 1) (hb : d310761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245662 q = 1) (hb : d310756 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245662, d310756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94058 q ha hb
    | true =>
      simp only [d245662, d310756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245663 q = 1) (hb : d310757 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245663, d310757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245663, d310757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245664 q = 1) (hb : d310758 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245664, d310758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245664, d310758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245665 q = 1) (hb : d310759 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245665, d310759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245665, d310759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245666 q = 1) (hb : d310760 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245666, d310760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245666, d310760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245667 q = 1) (hb : d310761 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245667, d310761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245667, d310761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94060 (p : Pattern) (ha : d245673 p = 1) (hb : d310767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245668 q = 1) (hb : d310762 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245668, d310762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94059 q ha hb
    | true =>
      simp only [d245668, d310762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245669 q = 1) (hb : d310763 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245669, d310763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245669, d310763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245670 q = 1) (hb : d310764 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245670, d310764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245670, d310764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245671 q = 1) (hb : d310765 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245671, d310765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245671, d310765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245672 q = 1) (hb : d310766 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245672, d310766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245672, d310766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245673 q = 1) (hb : d310767 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245673, d310767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245673, d310767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94061 (p : Pattern) (ha : d245679 p = 1) (hb : d310773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245674 q = 1) (hb : d310768 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245674, d310768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94060 q ha hb
    | true =>
      simp only [d245674, d310768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245675 q = 1) (hb : d310769 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245675, d310769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245675, d310769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245676 q = 1) (hb : d310770 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245676, d310770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245676, d310770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245677 q = 1) (hb : d310771 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245677, d310771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245677, d310771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245678 q = 1) (hb : d310772 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245678, d310772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245678, d310772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245679 q = 1) (hb : d310773 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245679, d310773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245679, d310773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94062 (p : Pattern) (ha : d2000 p = 1) (hb : d287735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2000 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2000, d287735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2000, d287735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro94063 (p : Pattern) (ha : d2015 p = 1) (hb : d287735 p = 1) : d32687 p = 1 := by
  have h0 (q : Pattern) (ha : d1999 q = 1) (hb : d253269 q = 1) : d1999 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2015 q = 1) (hb : d287735 q = 1) : d32687 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2015, d287735, d32687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2015, d287735, d32687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro94064 (p : Pattern) (ha : d30087 p = 1) (hb : d287735 p = 1) : d32693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94062 q ha hb
    | true =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30079 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30080 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30081 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30082 q = 1) (hb : d287735 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94063 q ha hb
    | true =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30083 q = 1) (hb : d287735 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30084 q = 1) (hb : d287735 q = 1) : d32690 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, d32690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30084, d32690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30085 q = 1) (hb : d287735 q = 1) : d32691 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, d32691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30085, d32691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30086 q = 1) (hb : d287735 q = 1) : d32692 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, d32692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30086, d32692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30087 q = 1) (hb : d287735 q = 1) : d32693 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30087, d32693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30087, d32693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94065 (p : Pattern) (ha : d2039 p = 1) (hb : d287735 p = 1) : d32701 p = 1 := by
  have h0 (q : Pattern) (ha : d2014 q = 1) (hb : d253269 q = 1) : d2014 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2039 q = 1) (hb : d287735 q = 1) : d32701 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2039, d287735, d32701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2039, d287735, d32701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro94066 (p : Pattern) (ha : d30097 p = 1) (hb : d287735 p = 1) : d281711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94062 q ha hb
    | true =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30082 q = 1) (hb : d287735 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94063 q ha hb
    | true =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30083 q = 1) (hb : d287735 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30084 q = 1) (hb : d287735 q = 1) : d32690 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, d32690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30084, d32690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30085 q = 1) (hb : d287735 q = 1) : d32691 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, d32691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30085, d32691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30086 q = 1) (hb : d287735 q = 1) : d32692 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, d32692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30086, d32692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30092 q = 1) (hb : d287735 q = 1) : d32702 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30092, d32702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94065 q ha hb
    | true =>
      simp only [d30092, d32702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30093 q = 1) (hb : d287735 q = 1) : d32703 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30093, d32703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30093, d32703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30094 q = 1) (hb : d287735 q = 1) : d281708 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30094, d281708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30094, d281708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30095 q = 1) (hb : d287735 q = 1) : d281709 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30095, d281709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30095, d281709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30096 q = 1) (hb : d287735 q = 1) : d281710 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30096, d281710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30096, d281710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30097 q = 1) (hb : d287735 q = 1) : d281711 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30097, d281711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30097, d281711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro94067 (p : Pattern) (ha : d39704 p = 1) (hb : d287735 p = 1) : d297516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d287735 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94063 q ha hb
    | true =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d287735 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30092 q = 1) (hb : d287735 q = 1) : d32702 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30092, d32702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94065 q ha hb
    | true =>
      simp only [d30092, d32702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30093 q = 1) (hb : d287735 q = 1) : d32703 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30093, d32703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30093, d32703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30094 q = 1) (hb : d287735 q = 1) : d281708 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30094, d281708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30094, d281708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30095 q = 1) (hb : d287735 q = 1) : d281709 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30095, d281709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30095, d281709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30096 q = 1) (hb : d287735 q = 1) : d281710 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30096, d281710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30096, d281710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32714 q = 1) (hb : d287735 q = 1) : d32714 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d39704 q = 1) (hb : d287735 q = 1) : d297516 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39704, d297516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39704, d297516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro94068 (p : Pattern) (ha : d39710 p = 1) (hb : d287735 p = 1) : d297522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30088 q = 1) (hb : d287735 q = 1) : d32694 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d32694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94064 q ha hb
    | true =>
      simp only [d30088, d32694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30089 q = 1) (hb : d287735 q = 1) : d32695 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d32695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30089, d32695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30090 q = 1) (hb : d287735 q = 1) : d32696 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30090, d32696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30090, d32696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30091 q = 1) (hb : d287735 q = 1) : d32697 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30091, d32697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30091, d32697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30098 q = 1) (hb : d287735 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94066 q ha hb
    | true =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30099 q = 1) (hb : d287735 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30100 q = 1) (hb : d287735 q = 1) : d281714 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30101 q = 1) (hb : d287735 q = 1) : d281715 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30101, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30102 q = 1) (hb : d287735 q = 1) : d281716 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30102, d281716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30102, d281716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39705 q = 1) (hb : d287735 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94067 q ha hb
    | true =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39706 q = 1) (hb : d287735 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39707 q = 1) (hb : d287735 q = 1) : d297519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39707, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39707, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39708 q = 1) (hb : d287735 q = 1) : d297520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39708, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39708, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d39709 q = 1) (hb : d287735 q = 1) : d297521 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39709, d297521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39709, d297521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39710 q = 1) (hb : d287735 q = 1) : d297522 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39710, d297522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39710, d297522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94069 (p : Pattern) (ha : d39716 p = 1) (hb : d287735 p = 1) : d297526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94062 q ha hb
    | true =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30082 q = 1) (hb : d287735 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94063 q ha hb
    | true =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30083 q = 1) (hb : d287735 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30084 q = 1) (hb : d287735 q = 1) : d32690 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, d32690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30084, d32690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30085 q = 1) (hb : d287735 q = 1) : d32691 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, d32691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30085, d32691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30086 q = 1) (hb : d287735 q = 1) : d32692 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, d32692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30086, d32692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2046 q = 1) (hb : d287735 q = 1) : d2046 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d39711 q = 1) (hb : d287735 q = 1) : d32722 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d39711, d32722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94065 q ha hb
    | true =>
      simp only [d39711, d32722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39712 q = 1) (hb : d287735 q = 1) : d32723 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d39712, d32723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39712, d32723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39713 q = 1) (hb : d287735 q = 1) : d297523 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d39713, d297523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39713, d297523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30103 q = 1) (hb : d287735 q = 1) : d30103 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d39714 q = 1) (hb : d287735 q = 1) : d297524 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d39714, d297524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d39714, d297524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39715 q = 1) (hb : d287735 q = 1) : d297525 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d39715, d297525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39715, d297525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39716 q = 1) (hb : d287735 q = 1) : d297526 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39716, d297526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39716, d297526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94070 (p : Pattern) (ha : d39721 p = 1) (hb : d287735 p = 1) : d297531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d287735 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94063 q ha hb
    | true =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d287735 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2046 q = 1) (hb : d287735 q = 1) : d2046 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d39711 q = 1) (hb : d287735 q = 1) : d32722 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d39711, d32722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94065 q ha hb
    | true =>
      simp only [d39711, d32722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39712 q = 1) (hb : d287735 q = 1) : d32723 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d39712, d32723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39712, d32723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39713 q = 1) (hb : d287735 q = 1) : d297523 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d39713, d297523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39713, d297523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30103 q = 1) (hb : d287735 q = 1) : d30103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d39714 q = 1) (hb : d287735 q = 1) : d297524 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d39714, d297524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39714, d297524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d39715 q = 1) (hb : d287735 q = 1) : d297525 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d39715, d297525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39715, d297525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d32714 q = 1) (hb : d287735 q = 1) : d32714 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d39721 q = 1) (hb : d287735 q = 1) : d297531 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39721, d297531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39721, d297531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94071 (p : Pattern) (ha : d39728 p = 1) (hb : d287735 p = 1) : d297538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39717 q = 1) (hb : d287735 q = 1) : d297527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94069 q ha hb
    | true =>
      simp only [d39717, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39718 q = 1) (hb : d287735 q = 1) : d297528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39718, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39719 q = 1) (hb : d287735 q = 1) : d297529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39719, d297529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39719, d297529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39720 q = 1) (hb : d287735 q = 1) : d297530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39720, d297530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39720, d297530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39722 q = 1) (hb : d287735 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94070 q ha hb
    | true =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39723 q = 1) (hb : d287735 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39724 q = 1) (hb : d287735 q = 1) : d297534 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39724, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39724, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39725 q = 1) (hb : d287735 q = 1) : d297535 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39725, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39725, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39726 q = 1) (hb : d287735 q = 1) : d297536 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39726, d297536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39726, d297536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39705 q = 1) (hb : d287735 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94067 q ha hb
    | true =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39706 q = 1) (hb : d287735 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39707 q = 1) (hb : d287735 q = 1) : d297519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39707, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39707, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39708 q = 1) (hb : d287735 q = 1) : d297520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39708, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39708, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d39727 q = 1) (hb : d287735 q = 1) : d297537 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39727, d297537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39727, d297537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39728 q = 1) (hb : d287735 q = 1) : d297538 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39728, d297538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39728, d297538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94072 (p : Pattern) (ha : d39733 p = 1) (hb : d287735 p = 1) : d297543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39722 q = 1) (hb : d287735 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94070 q ha hb
    | true =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39723 q = 1) (hb : d287735 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39724 q = 1) (hb : d287735 q = 1) : d297534 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39724, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39724, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39725 q = 1) (hb : d287735 q = 1) : d297535 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39725, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39725, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39732 q = 1) (hb : d287735 q = 1) : d297542 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39732, d297542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39732, d297542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15557 q = 1) (hb : d287735 q = 1) : d15557 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d39733 q = 1) (hb : d287735 q = 1) : d297543 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39733, d297543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39733, d297543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro94073 (p : Pattern) (ha : d39740 p = 1) (hb : d287735 p = 1) : d297550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39729 q = 1) (hb : d287735 q = 1) : d297539 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39729, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94068 q ha hb
    | true =>
      simp only [d39729, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94071 q ha hb
  have h2 (q : Pattern) (ha : d39730 q = 1) (hb : d287735 q = 1) : d297540 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39730, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39730, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39731 q = 1) (hb : d287735 q = 1) : d297541 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39731, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39731, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39734 q = 1) (hb : d287735 q = 1) : d297544 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94071 q ha hb
    | true =>
      simp only [d39734, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94072 q ha hb
  have h5 (q : Pattern) (ha : d39735 q = 1) (hb : d287735 q = 1) : d297545 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39736 q = 1) (hb : d287735 q = 1) : d297546 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39737 q = 1) (hb : d287735 q = 1) : d297547 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39737, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39737, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39738 q = 1) (hb : d287735 q = 1) : d297548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39738, d297548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39738, d297548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39739 q = 1) (hb : d287735 q = 1) : d297549 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39739, d297549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39739, d297549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39740 q = 1) (hb : d287735 q = 1) : d297550 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39740, d297550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39740, d297550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro94074 (p : Pattern) (ha : d39744 p = 1) (hb : d287735 p = 1) : d297554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39734 q = 1) (hb : d287735 q = 1) : d297544 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94071 q ha hb
    | true =>
      simp only [d39734, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94072 q ha hb
  have h2 (q : Pattern) (ha : d39735 q = 1) (hb : d287735 q = 1) : d297545 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39736 q = 1) (hb : d287735 q = 1) : d297546 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39738 q = 1) (hb : d287735 q = 1) : d297548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39738, d297548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39738, d297548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39743 q = 1) (hb : d287735 q = 1) : d297553 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39743, d297553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39743, d297553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39744 q = 1) (hb : d287735 q = 1) : d297554 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39744, d297554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39744, d297554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94075 (p : Pattern) (ha : d39750 p = 1) (hb : d287735 p = 1) : d297560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d287735 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94073 q ha hb
    | true =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d287735 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d287735 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d287735 q = 1) : d297558 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39749 q = 1) (hb : d287735 q = 1) : d297559 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39749, d297559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39749, d297559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39750 q = 1) (hb : d287735 q = 1) : d297560 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39750, d297560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39750, d297560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94076 (p : Pattern) (ha : d39754 p = 1) (hb : d287735 p = 1) : d297564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d287735 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d287735 q = 1) : d297562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39753 q = 1) (hb : d287735 q = 1) : d297563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39753, d297563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39753, d297563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39754 q = 1) (hb : d287735 q = 1) : d297564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39754, d297564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39754, d297564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94077 (p : Pattern) (ha : d39760 p = 1) (hb : d287735 p = 1) : d297570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39755 q = 1) (hb : d287735 q = 1) : d297565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39755, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94075 q ha hb
    | true =>
      simp only [d39755, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94076 q ha hb
  have h2 (q : Pattern) (ha : d39756 q = 1) (hb : d287735 q = 1) : d297566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39756, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39756, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39757 q = 1) (hb : d287735 q = 1) : d297567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39757, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39757, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39758 q = 1) (hb : d287735 q = 1) : d297568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39758, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39758, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39759 q = 1) (hb : d287735 q = 1) : d297569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39759, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39759, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39760 q = 1) (hb : d287735 q = 1) : d297570 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39760, d297570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39760, d297570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94078 (p : Pattern) (ha : d39763 p = 1) (hb : d287735 p = 1) : d297573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d287735 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94073 q ha hb
    | true =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d287735 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d287735 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d287735 q = 1) : d297558 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39749 q = 1) (hb : d287735 q = 1) : d297559 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39749, d297559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39749, d297559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39763 q = 1) (hb : d287735 q = 1) : d297573 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39763, d297573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39763, d297573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94079 (p : Pattern) (ha : d39764 p = 1) (hb : d287735 p = 1) : d297574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d287735 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d287735 q = 1) : d297562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39753 q = 1) (hb : d287735 q = 1) : d297563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39753, d297563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39753, d297563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39764 q = 1) (hb : d287735 q = 1) : d297574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39764, d297574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39764, d297574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94080 (p : Pattern) (ha : d39770 p = 1) (hb : d287735 p = 1) : d297580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39755 q = 1) (hb : d287735 q = 1) : d297565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39755, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94075 q ha hb
    | true =>
      simp only [d39755, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94076 q ha hb
  have h2 (q : Pattern) (ha : d39756 q = 1) (hb : d287735 q = 1) : d297566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39756, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39756, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39757 q = 1) (hb : d287735 q = 1) : d297567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39757, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39757, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39758 q = 1) (hb : d287735 q = 1) : d297568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39758, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39758, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39759 q = 1) (hb : d287735 q = 1) : d297569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39759, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39759, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39765 q = 1) (hb : d287735 q = 1) : d297575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39765, d297575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94078 q ha hb
    | true =>
      simp only [d39765, d297575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94079 q ha hb
  have h7 (q : Pattern) (ha : d39766 q = 1) (hb : d287735 q = 1) : d297576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39766, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39766, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39767 q = 1) (hb : d287735 q = 1) : d297577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39767, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39767, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39768 q = 1) (hb : d287735 q = 1) : d297578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39768, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39768, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39769 q = 1) (hb : d287735 q = 1) : d297579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39769, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39769, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39770 q = 1) (hb : d287735 q = 1) : d297580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39770, d297580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39770, d297580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94081 (p : Pattern) (ha : d39926 p = 1) (hb : d287735 p = 1) : d297681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39755 q = 1) (hb : d287735 q = 1) : d297565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39755, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94075 q ha hb
    | true =>
      simp only [d39755, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94076 q ha hb
  have h2 (q : Pattern) (ha : d39756 q = 1) (hb : d287735 q = 1) : d297566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39756, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39756, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39757 q = 1) (hb : d287735 q = 1) : d297567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39757, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39757, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39758 q = 1) (hb : d287735 q = 1) : d297568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39758, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39758, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39759 q = 1) (hb : d287735 q = 1) : d297569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39759, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39759, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39921 q = 1) (hb : d287735 q = 1) : d297676 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39921, d297676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94076 q ha hb
    | true =>
      simp only [d39921, d297676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39922 q = 1) (hb : d287735 q = 1) : d297677 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39922, d297677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39922, d297677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39923 q = 1) (hb : d287735 q = 1) : d297678 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39923, d297678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39923, d297678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39924 q = 1) (hb : d287735 q = 1) : d297679 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39924, d297679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39924, d297679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39925 q = 1) (hb : d287735 q = 1) : d297680 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39925, d297680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39925, d297680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39926 q = 1) (hb : d287735 q = 1) : d297681 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39926, d297681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39926, d297681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94082 (p : Pattern) (ha : d39932 p = 1) (hb : d287735 p = 1) : d297687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39921 q = 1) (hb : d287735 q = 1) : d297676 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39921, d297676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94076 q ha hb
    | true =>
      simp only [d39921, d297676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39922 q = 1) (hb : d287735 q = 1) : d297677 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39922, d297677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39922, d297677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39923 q = 1) (hb : d287735 q = 1) : d297678 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39923, d297678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39923, d297678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39924 q = 1) (hb : d287735 q = 1) : d297679 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39924, d297679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39924, d297679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39925 q = 1) (hb : d287735 q = 1) : d297680 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39925, d297680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39925, d297680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39927 q = 1) (hb : d287735 q = 1) : d297682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39927, d297682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94079 q ha hb
    | true =>
      simp only [d39927, d297682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39928 q = 1) (hb : d287735 q = 1) : d297683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39928, d297683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39928, d297683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39929 q = 1) (hb : d287735 q = 1) : d297684 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39929, d297684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39929, d297684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39930 q = 1) (hb : d287735 q = 1) : d297685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39930, d297685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39930, d297685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39931 q = 1) (hb : d287735 q = 1) : d297686 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39931, d297686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39931, d297686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39932 q = 1) (hb : d287735 q = 1) : d297687 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39932, d297687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39932, d297687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94083 (p : Pattern) (ha : d39941 p = 1) (hb : d287735 p = 1) : d297696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39927 q = 1) (hb : d287735 q = 1) : d297682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39927, d297682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94079 q ha hb
    | true =>
      simp only [d39927, d297682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39928 q = 1) (hb : d287735 q = 1) : d297683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39928, d297683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39928, d297683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39929 q = 1) (hb : d287735 q = 1) : d297684 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39929, d297684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39929, d297684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39930 q = 1) (hb : d287735 q = 1) : d297685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39930, d297685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39930, d297685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39931 q = 1) (hb : d287735 q = 1) : d297686 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39931, d297686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39931, d297686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39941 q = 1) (hb : d287735 q = 1) : d297696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39941, d297696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39941, d297696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94084 (p : Pattern) (ha : d39971 p = 1) (hb : d287735 p = 1) : d297726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39962 q = 1) (hb : d287735 q = 1) : d297717 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39962, d297717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39962, d297717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94069 q ha hb
  have h2 (q : Pattern) (ha : d39717 q = 1) (hb : d287735 q = 1) : d297527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94069 q ha hb
    | true =>
      simp only [d39717, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39963 q = 1) (hb : d287735 q = 1) : d297718 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39963, d297718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39963, d297718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39718 q = 1) (hb : d287735 q = 1) : d297528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39718, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39964 q = 1) (hb : d287735 q = 1) : d297719 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39964, d297719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39964, d297719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39965 q = 1) (hb : d287735 q = 1) : d297720 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39965, d297720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39965, d297720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39966 q = 1) (hb : d287735 q = 1) : d297721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39966, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39966, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94070 q ha hb
  have h8 (q : Pattern) (ha : d39722 q = 1) (hb : d287735 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94070 q ha hb
    | true =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39967 q = 1) (hb : d287735 q = 1) : d297722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39967, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39967, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39723 q = 1) (hb : d287735 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39968 q = 1) (hb : d287735 q = 1) : d297723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39968, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39968, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d39969 q = 1) (hb : d287735 q = 1) : d297724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39969, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d39969, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d39970 q = 1) (hb : d287735 q = 1) : d297725 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39970, d297725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39970, d297725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39947 q = 1) (hb : d287735 q = 1) : d297702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39947, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39947, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94067 q ha hb
  have h15 (q : Pattern) (ha : d39705 q = 1) (hb : d287735 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94067 q ha hb
    | true =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d39948 q = 1) (hb : d287735 q = 1) : d297703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39948, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d39948, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39706 q = 1) (hb : d287735 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d39949 q = 1) (hb : d287735 q = 1) : d297704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39949, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d39949, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d39950 q = 1) (hb : d287735 q = 1) : d297705 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39950, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d39950, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d39956 q = 1) (hb : d287735 q = 1) : d297711 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39956, d297711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d39956, d297711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d39971 q = 1) (hb : d287735 q = 1) : d297726 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39971, d297726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39971, d297726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro94085 (p : Pattern) (ha : d39976 p = 1) (hb : d287735 p = 1) : d297731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39966 q = 1) (hb : d287735 q = 1) : d297721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39966, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39966, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94070 q ha hb
  have h2 (q : Pattern) (ha : d39722 q = 1) (hb : d287735 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94070 q ha hb
    | true =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39967 q = 1) (hb : d287735 q = 1) : d297722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39967, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39967, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39723 q = 1) (hb : d287735 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39968 q = 1) (hb : d287735 q = 1) : d297723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39968, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39968, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39969 q = 1) (hb : d287735 q = 1) : d297724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39969, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39969, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39975 q = 1) (hb : d287735 q = 1) : d297730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39975, d297730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39975, d297730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15794 q = 1) (hb : d287735 q = 1) : d15794 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d39976 q = 1) (hb : d287735 q = 1) : d297731 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39976, d297731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39976, d297731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro94086 (p : Pattern) (ha : d39995 p = 1) (hb : d287735 p = 1) : d297750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39977 q = 1) (hb : d287735 q = 1) : d297732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39977, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94084 q ha hb
    | true =>
      simp only [d39977, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94085 q ha hb
  have h2 (q : Pattern) (ha : d39978 q = 1) (hb : d287735 q = 1) : d297733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39978, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39978, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39979 q = 1) (hb : d287735 q = 1) : d297734 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39979, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39979, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39985 q = 1) (hb : d287735 q = 1) : d297740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39985, d297740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39985, d297740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39994 q = 1) (hb : d287735 q = 1) : d297749 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39994, d297749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39994, d297749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39995 q = 1) (hb : d287735 q = 1) : d297750 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39995, d297750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39995, d297750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94087 (p : Pattern) (ha : d40082 p = 1) (hb : d287735 p = 1) : d297793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39996 q = 1) (hb : d287735 q = 1) : d297751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39996, d297751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94086 q ha hb
    | true =>
      simp only [d39996, d297751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39997 q = 1) (hb : d287735 q = 1) : d297752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39997, d297752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39997, d297752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40079 q = 1) (hb : d287735 q = 1) : d297790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40079, d297790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40079, d297790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40080 q = 1) (hb : d287735 q = 1) : d297791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40080, d297791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40080, d297791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40081 q = 1) (hb : d287735 q = 1) : d297792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40081, d297792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40081, d297792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40082 q = 1) (hb : d287735 q = 1) : d297793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40082, d297793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40082, d297793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94088 (p : Pattern) (ha : d40088 p = 1) (hb : d287735 p = 1) : d297799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40083 q = 1) (hb : d287735 q = 1) : d297794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40083, d297794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94087 q ha hb
    | true =>
      simp only [d40083, d297794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40084 q = 1) (hb : d287735 q = 1) : d297795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40084, d297795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40084, d297795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40085 q = 1) (hb : d287735 q = 1) : d297796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40085, d297796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40085, d297796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40086 q = 1) (hb : d287735 q = 1) : d297797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40086, d297797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40086, d297797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40087 q = 1) (hb : d287735 q = 1) : d297798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40087, d297798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40087, d297798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40088 q = 1) (hb : d287735 q = 1) : d297799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40088, d297799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40088, d297799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94089 (p : Pattern) (ha : d39775 p = 1) (hb : d287735 p = 1) : d297585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d287735 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94073 q ha hb
    | true =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d287735 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d287735 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d287735 q = 1) : d297558 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39774 q = 1) (hb : d287735 q = 1) : d297584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39774, d297584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39774, d297584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39775 q = 1) (hb : d287735 q = 1) : d297585 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39775, d297585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39775, d297585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94090 (p : Pattern) (ha : d39777 p = 1) (hb : d287735 p = 1) : d297587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d287735 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d287735 q = 1) : d297562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39776 q = 1) (hb : d287735 q = 1) : d297586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39776, d297586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39776, d297586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39777 q = 1) (hb : d287735 q = 1) : d297587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39777, d297587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39777, d297587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94091 (p : Pattern) (ha : d39784 p = 1) (hb : d287735 p = 1) : d297594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d287735 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94073 q ha hb
    | true =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d287735 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d287735 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39782 q = 1) (hb : d287735 q = 1) : d297592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39782, d297592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39782, d297592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39783 q = 1) (hb : d287735 q = 1) : d297593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39783, d297593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39783, d297593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39784 q = 1) (hb : d287735 q = 1) : d297594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39784, d297594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39784, d297594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94092 (p : Pattern) (ha : d39787 p = 1) (hb : d287735 p = 1) : d297597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d287735 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39785 q = 1) (hb : d287735 q = 1) : d297595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39785, d297595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39785, d297595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39786 q = 1) (hb : d287735 q = 1) : d297596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39786, d297596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39786, d297596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39787 q = 1) (hb : d287735 q = 1) : d297597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39787, d297597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39787, d297597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94093 (p : Pattern) (ha : d30198 p = 1) (hb : d287735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94062 q ha hb
    | true =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30079 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30080 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30081 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30198 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94094 (p : Pattern) (ha : d30204 p = 1) (hb : d287735 p = 1) : d281801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30199 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94093 q ha hb
    | true =>
      simp only [d30199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30200 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30201 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30202 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30088 q = 1) (hb : d287735 q = 1) : d32694 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d32694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94064 q ha hb
    | true =>
      simp only [d30088, d32694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30089 q = 1) (hb : d287735 q = 1) : d32695 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d32695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30089, d32695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30090 q = 1) (hb : d287735 q = 1) : d32696 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30090, d32696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30090, d32696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30091 q = 1) (hb : d287735 q = 1) : d32697 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30091, d32697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30091, d32697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30203 q = 1) (hb : d287735 q = 1) : d32802 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30203, d32802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30203, d32802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30098 q = 1) (hb : d287735 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94066 q ha hb
    | true =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30099 q = 1) (hb : d287735 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30100 q = 1) (hb : d287735 q = 1) : d281714 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30101 q = 1) (hb : d287735 q = 1) : d281715 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30101, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30102 q = 1) (hb : d287735 q = 1) : d281716 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30102, d281716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30102, d281716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30204 q = 1) (hb : d287735 q = 1) : d281801 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30204, d281801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30204, d281801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94095 (p : Pattern) (ha : d39794 p = 1) (hb : d287735 p = 1) : d297604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30098 q = 1) (hb : d287735 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94066 q ha hb
    | true =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30099 q = 1) (hb : d287735 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30100 q = 1) (hb : d287735 q = 1) : d281714 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30101 q = 1) (hb : d287735 q = 1) : d281715 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30101, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39705 q = 1) (hb : d287735 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94067 q ha hb
    | true =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39706 q = 1) (hb : d287735 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39707 q = 1) (hb : d287735 q = 1) : d297519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39707, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39707, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39708 q = 1) (hb : d287735 q = 1) : d297520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39708, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39708, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39709 q = 1) (hb : d287735 q = 1) : d297521 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39709, d297521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39709, d297521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39727 q = 1) (hb : d287735 q = 1) : d297537 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39727, d297537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39727, d297537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39794 q = 1) (hb : d287735 q = 1) : d297604 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39794, d297604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39794, d297604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94096 (p : Pattern) (ha : d39800 p = 1) (hb : d287735 p = 1) : d297610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39791 q = 1) (hb : d287735 q = 1) : d297601 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39791, d297601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94094 q ha hb
    | true =>
      simp only [d39791, d297601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94068 q ha hb
  have h2 (q : Pattern) (ha : d39792 q = 1) (hb : d287735 q = 1) : d297602 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39792, d297602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39792, d297602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39793 q = 1) (hb : d287735 q = 1) : d297603 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39793, d297603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39793, d297603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39795 q = 1) (hb : d287735 q = 1) : d297605 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39795, d297605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94068 q ha hb
    | true =>
      simp only [d39795, d297605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94095 q ha hb
  have h5 (q : Pattern) (ha : d39796 q = 1) (hb : d287735 q = 1) : d297606 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39796, d297606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39796, d297606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39797 q = 1) (hb : d287735 q = 1) : d297607 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39797, d297607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39797, d297607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39798 q = 1) (hb : d287735 q = 1) : d297608 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39798, d297608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39798, d297608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39729 q = 1) (hb : d287735 q = 1) : d297539 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39729, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94068 q ha hb
    | true =>
      simp only [d39729, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94071 q ha hb
  have h9 (q : Pattern) (ha : d39730 q = 1) (hb : d287735 q = 1) : d297540 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39730, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39730, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39731 q = 1) (hb : d287735 q = 1) : d297541 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39731, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39731, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39734 q = 1) (hb : d287735 q = 1) : d297544 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94071 q ha hb
    | true =>
      simp only [d39734, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94072 q ha hb
  have h12 (q : Pattern) (ha : d39735 q = 1) (hb : d287735 q = 1) : d297545 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39736 q = 1) (hb : d287735 q = 1) : d297546 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39737 q = 1) (hb : d287735 q = 1) : d297547 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39737, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39737, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39799 q = 1) (hb : d287735 q = 1) : d297609 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39799, d297609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39799, d297609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d39800 q = 1) (hb : d287735 q = 1) : d297610 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39800, d297610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39800, d297610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro94097 (p : Pattern) (ha : d39806 p = 1) (hb : d287735 p = 1) : d297616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39801 q = 1) (hb : d287735 q = 1) : d297611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39801, d297611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94096 q ha hb
    | true =>
      simp only [d39801, d297611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39802 q = 1) (hb : d287735 q = 1) : d297612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39802, d297612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39802, d297612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39741 q = 1) (hb : d287735 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94073 q ha hb
    | true =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39742 q = 1) (hb : d287735 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39803 q = 1) (hb : d287735 q = 1) : d297613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39803, d297613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39803, d297613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39804 q = 1) (hb : d287735 q = 1) : d297614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39804, d297614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39804, d297614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39805 q = 1) (hb : d287735 q = 1) : d297615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39805, d297615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39805, d297615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39806 q = 1) (hb : d287735 q = 1) : d297616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39806, d297616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39806, d297616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94098 (p : Pattern) (ha : d39861 p = 1) (hb : d287735 p = 1) : d297619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d287735 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94063 q ha hb
    | true =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d287735 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30309 q = 1) (hb : d287735 q = 1) : d281820 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30309, d281820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30309, d281820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30310 q = 1) (hb : d287735 q = 1) : d281821 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30310, d281821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30310, d281821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30311 q = 1) (hb : d287735 q = 1) : d281822 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30311, d281822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30311, d281822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5245 q = 1) (hb : d287735 q = 1) : d5245 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d39861 q = 1) (hb : d287735 q = 1) : d297619 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39861, d297619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39861, d297619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro94099 (p : Pattern) (ha : d39867 p = 1) (hb : d287735 p = 1) : d297625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39717 q = 1) (hb : d287735 q = 1) : d297527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94069 q ha hb
    | true =>
      simp only [d39717, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39718 q = 1) (hb : d287735 q = 1) : d297528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39718, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39719 q = 1) (hb : d287735 q = 1) : d297529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39719, d297529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39719, d297529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39720 q = 1) (hb : d287735 q = 1) : d297530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39720, d297530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39720, d297530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39722 q = 1) (hb : d287735 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94070 q ha hb
    | true =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39723 q = 1) (hb : d287735 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39724 q = 1) (hb : d287735 q = 1) : d297534 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39724, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39724, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39725 q = 1) (hb : d287735 q = 1) : d297535 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39725, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39725, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39726 q = 1) (hb : d287735 q = 1) : d297536 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39726, d297536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39726, d297536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39862 q = 1) (hb : d287735 q = 1) : d297620 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39862, d297620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94098 q ha hb
    | true =>
      simp only [d39862, d297620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39863 q = 1) (hb : d287735 q = 1) : d297621 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39863, d297621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39863, d297621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39864 q = 1) (hb : d287735 q = 1) : d297622 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39864, d297622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39864, d297622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39865 q = 1) (hb : d287735 q = 1) : d297623 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39865, d297623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39865, d297623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d39866 q = 1) (hb : d287735 q = 1) : d297624 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39866, d297624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39866, d297624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39867 q = 1) (hb : d287735 q = 1) : d297625 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39867, d297625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39867, d297625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94100 (p : Pattern) (ha : d39871 p = 1) (hb : d287735 p = 1) : d297629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d287735 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94063 q ha hb
    | true =>
      simp only [d30082, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d287735 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d287735 q = 1) : d5239 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d39868 q = 1) (hb : d287735 q = 1) : d297626 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d39868, d297626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39868, d297626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30103 q = 1) (hb : d287735 q = 1) : d30103 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d39869 q = 1) (hb : d287735 q = 1) : d297627 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d39869, d297627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39869, d297627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39870 q = 1) (hb : d287735 q = 1) : d297628 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d39870, d297628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39870, d297628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5245 q = 1) (hb : d287735 q = 1) : d5245 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d39871 q = 1) (hb : d287735 q = 1) : d297629 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39871, d297629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39871, d297629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro94101 (p : Pattern) (ha : d39877 p = 1) (hb : d287735 p = 1) : d297635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39872 q = 1) (hb : d287735 q = 1) : d297630 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39872, d297630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94100 q ha hb
    | true =>
      simp only [d39872, d297630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39873 q = 1) (hb : d287735 q = 1) : d297631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39873, d297631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39873, d297631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39874 q = 1) (hb : d287735 q = 1) : d297632 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39874, d297632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39874, d297632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39875 q = 1) (hb : d287735 q = 1) : d297633 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39875, d297633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39875, d297633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39876 q = 1) (hb : d287735 q = 1) : d297634 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39876, d297634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39876, d297634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39877 q = 1) (hb : d287735 q = 1) : d297635 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39877, d297635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39877, d297635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94102 (p : Pattern) (ha : d39883 p = 1) (hb : d287735 p = 1) : d297641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39729 q = 1) (hb : d287735 q = 1) : d297539 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39729, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94068 q ha hb
    | true =>
      simp only [d39729, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94071 q ha hb
  have h2 (q : Pattern) (ha : d39730 q = 1) (hb : d287735 q = 1) : d297540 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39730, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39730, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39731 q = 1) (hb : d287735 q = 1) : d297541 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39731, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39731, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39734 q = 1) (hb : d287735 q = 1) : d297544 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94071 q ha hb
    | true =>
      simp only [d39734, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94072 q ha hb
  have h5 (q : Pattern) (ha : d39735 q = 1) (hb : d287735 q = 1) : d297545 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39736 q = 1) (hb : d287735 q = 1) : d297546 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39737 q = 1) (hb : d287735 q = 1) : d297547 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39737, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39737, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39878 q = 1) (hb : d287735 q = 1) : d297636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39878, d297636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94099 q ha hb
    | true =>
      simp only [d39878, d297636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94101 q ha hb
  have h9 (q : Pattern) (ha : d39879 q = 1) (hb : d287735 q = 1) : d297637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39879, d297637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39879, d297637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39880 q = 1) (hb : d287735 q = 1) : d297638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39880, d297638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39880, d297638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39881 q = 1) (hb : d287735 q = 1) : d297639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39881, d297639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39881, d297639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39882 q = 1) (hb : d287735 q = 1) : d297640 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39882, d297640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39882, d297640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39883 q = 1) (hb : d287735 q = 1) : d297641 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39883, d297641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39883, d297641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro94103 (p : Pattern) (ha : d39889 p = 1) (hb : d287735 p = 1) : d297647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39884 q = 1) (hb : d287735 q = 1) : d297642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39884, d297642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94102 q ha hb
    | true =>
      simp only [d39884, d297642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39885 q = 1) (hb : d287735 q = 1) : d297643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39885, d297643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39885, d297643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39886 q = 1) (hb : d287735 q = 1) : d297644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39886, d297644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39886, d297644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39887 q = 1) (hb : d287735 q = 1) : d297645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39887, d297645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39887, d297645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39888 q = 1) (hb : d287735 q = 1) : d297646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39888, d297646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39888, d297646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39889 q = 1) (hb : d287735 q = 1) : d297647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39889, d297647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39889, d297647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94104 (p : Pattern) (ha : d281023 p = 1) (hb : d287735 p = 1) : d297653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39778 q = 1) (hb : d287735 q = 1) : d297588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39778, d297588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94089 q ha hb
    | true =>
      simp only [d39778, d297588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94090 q ha hb
  have h2 (q : Pattern) (ha : d39779 q = 1) (hb : d287735 q = 1) : d297589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39779, d297589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39779, d297589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39780 q = 1) (hb : d287735 q = 1) : d297590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39780, d297590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39780, d297590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39781 q = 1) (hb : d287735 q = 1) : d297591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39781, d297591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39781, d297591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39788 q = 1) (hb : d287735 q = 1) : d297598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39788, d297598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94091 q ha hb
    | true =>
      simp only [d39788, d297598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94092 q ha hb
  have h6 (q : Pattern) (ha : d39789 q = 1) (hb : d287735 q = 1) : d297599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39789, d297599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39789, d297599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39790 q = 1) (hb : d287735 q = 1) : d297600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39790, d297600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39790, d297600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39807 q = 1) (hb : d287735 q = 1) : d297617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39807, d297617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94097 q ha hb
    | true =>
      simp only [d39807, d297617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94075 q ha hb
  have h9 (q : Pattern) (ha : d281019 q = 1) (hb : d287735 q = 1) : d297618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281019, d297618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d281019, d297618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d39890 q = 1) (hb : d287735 q = 1) : d297648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39890, d297648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94103 q ha hb
    | true =>
      simp only [d39890, d297648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39891 q = 1) (hb : d287735 q = 1) : d297649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39891, d297649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39891, d297649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d281020 q = 1) (hb : d287735 q = 1) : d297650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281020, d297650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d281020, d297650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d281021 q = 1) (hb : d287735 q = 1) : d297651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281021, d297651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d281021, d297651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d281022 q = 1) (hb : d287735 q = 1) : d297652 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281022, d297652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281022, d297652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d281023 q = 1) (hb : d287735 q = 1) : d297653 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281023, d297653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281023, d297653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94105 (p : Pattern) (ha : d39896 p = 1) (hb : d287735 p = 1) : d297654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d287735 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94073 q ha hb
    | true =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d287735 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d287735 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d287735 q = 1) : d297558 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39774 q = 1) (hb : d287735 q = 1) : d297584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39774, d297584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39774, d297584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39896 q = 1) (hb : d287735 q = 1) : d297654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39896, d297654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39896, d297654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94106 (p : Pattern) (ha : d39897 p = 1) (hb : d287735 p = 1) : d297655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d287735 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d287735 q = 1) : d297562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39776 q = 1) (hb : d287735 q = 1) : d297586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39776, d297586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39776, d297586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39897 q = 1) (hb : d287735 q = 1) : d297655 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39897, d297655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39897, d297655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94107 (p : Pattern) (ha : d39902 p = 1) (hb : d287735 p = 1) : d297660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d287735 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94073 q ha hb
    | true =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d287735 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d287735 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39782 q = 1) (hb : d287735 q = 1) : d297592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39782, d297592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39782, d297592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39783 q = 1) (hb : d287735 q = 1) : d297593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39783, d297593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39783, d297593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39902 q = 1) (hb : d287735 q = 1) : d297660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39902, d297660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39902, d297660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94108 (p : Pattern) (ha : d39903 p = 1) (hb : d287735 p = 1) : d297661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d287735 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94074 q ha hb
    | true =>
      simp only [d39745, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d287735 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d287735 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39785 q = 1) (hb : d287735 q = 1) : d297595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39785, d297595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39785, d297595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39786 q = 1) (hb : d287735 q = 1) : d297596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39786, d297596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39786, d297596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39903 q = 1) (hb : d287735 q = 1) : d297661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39903, d297661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39903, d297661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94109 (p : Pattern) (ha : d39907 p = 1) (hb : d287735 p = 1) : d297665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39801 q = 1) (hb : d287735 q = 1) : d297611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39801, d297611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94096 q ha hb
    | true =>
      simp only [d39801, d297611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39802 q = 1) (hb : d287735 q = 1) : d297612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39802, d297612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39802, d297612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39741 q = 1) (hb : d287735 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94073 q ha hb
    | true =>
      simp only [d39741, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39742 q = 1) (hb : d287735 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39803 q = 1) (hb : d287735 q = 1) : d297613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39803, d297613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39803, d297613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39804 q = 1) (hb : d287735 q = 1) : d297614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39804, d297614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39804, d297614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39805 q = 1) (hb : d287735 q = 1) : d297615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39805, d297615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39805, d297615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39907 q = 1) (hb : d287735 q = 1) : d297665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39907, d297665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39907, d297665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94110 (p : Pattern) (ha : d39913 p = 1) (hb : d287735 p = 1) : d297668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39884 q = 1) (hb : d287735 q = 1) : d297642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39884, d297642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94102 q ha hb
    | true =>
      simp only [d39884, d297642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39885 q = 1) (hb : d287735 q = 1) : d297643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39885, d297643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39885, d297643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39886 q = 1) (hb : d287735 q = 1) : d297644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39886, d297644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39886, d297644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39887 q = 1) (hb : d287735 q = 1) : d297645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39887, d297645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39887, d297645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39888 q = 1) (hb : d287735 q = 1) : d297646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39888, d297646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39888, d297646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39913 q = 1) (hb : d287735 q = 1) : d297668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39913, d297668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39913, d297668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94111 (p : Pattern) (ha : d281028 p = 1) (hb : d287735 p = 1) : d297674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39778 q = 1) (hb : d287735 q = 1) : d297588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39778, d297588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94089 q ha hb
    | true =>
      simp only [d39778, d297588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94090 q ha hb
  have h2 (q : Pattern) (ha : d39779 q = 1) (hb : d287735 q = 1) : d297589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39779, d297589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39779, d297589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39780 q = 1) (hb : d287735 q = 1) : d297590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39780, d297590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39780, d297590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39781 q = 1) (hb : d287735 q = 1) : d297591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39781, d297591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39781, d297591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39788 q = 1) (hb : d287735 q = 1) : d297598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39788, d297598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94091 q ha hb
    | true =>
      simp only [d39788, d297598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94092 q ha hb
  have h6 (q : Pattern) (ha : d39789 q = 1) (hb : d287735 q = 1) : d297599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39789, d297599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39789, d297599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39790 q = 1) (hb : d287735 q = 1) : d297600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39790, d297600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39790, d297600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39807 q = 1) (hb : d287735 q = 1) : d297617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39807, d297617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94097 q ha hb
    | true =>
      simp only [d39807, d297617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94075 q ha hb
  have h9 (q : Pattern) (ha : d281019 q = 1) (hb : d287735 q = 1) : d297618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281019, d297618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d281019, d297618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d39890 q = 1) (hb : d287735 q = 1) : d297648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39890, d297648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94103 q ha hb
    | true =>
      simp only [d39890, d297648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39891 q = 1) (hb : d287735 q = 1) : d297649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39891, d297649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39891, d297649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d281020 q = 1) (hb : d287735 q = 1) : d297650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281020, d297650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d281020, d297650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d281021 q = 1) (hb : d287735 q = 1) : d297651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281021, d297651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d281021, d297651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d281022 q = 1) (hb : d287735 q = 1) : d297652 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281022, d297652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281022, d297652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39898 q = 1) (hb : d287735 q = 1) : d297656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39898, d297656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94105 q ha hb
    | true =>
      simp only [d39898, d297656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94106 q ha hb
  have h16 (q : Pattern) (ha : d39899 q = 1) (hb : d287735 q = 1) : d297657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39899, d297657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39899, d297657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39900 q = 1) (hb : d287735 q = 1) : d297658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39900, d297658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d39900, d297658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d39901 q = 1) (hb : d287735 q = 1) : d297659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39901, d297659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39901, d297659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d39904 q = 1) (hb : d287735 q = 1) : d297662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39904, d297662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94107 q ha hb
    | true =>
      simp only [d39904, d297662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94108 q ha hb
  have h20 (q : Pattern) (ha : d39905 q = 1) (hb : d287735 q = 1) : d297663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39905, d297663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39905, d297663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d39906 q = 1) (hb : d287735 q = 1) : d297664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39906, d297664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d39906, d297664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d39908 q = 1) (hb : d287735 q = 1) : d297666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39908, d297666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94109 q ha hb
    | true =>
      simp only [d39908, d297666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94078 q ha hb
  have h23 (q : Pattern) (ha : d281024 q = 1) (hb : d287735 q = 1) : d297667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281024, d297667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d281024, d297667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d39914 q = 1) (hb : d287735 q = 1) : d297669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39914, d297669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94110 q ha hb
    | true =>
      simp only [d39914, d297669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d39915 q = 1) (hb : d287735 q = 1) : d297670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39915, d297670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d39915, d297670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d281025 q = 1) (hb : d287735 q = 1) : d297671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281025, d297671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d281025, d297671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d281026 q = 1) (hb : d287735 q = 1) : d297672 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281026, d297672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d281026, d297672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d281027 q = 1) (hb : d287735 q = 1) : d297673 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281027, d297673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d281027, d297673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d281028 q = 1) (hb : d287735 q = 1) : d297674 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281028, d297674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d281028, d297674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro94112 (p : Pattern) (ha : d281035 p = 1) (hb : d287735 p = 1) : d297694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39908 q = 1) (hb : d287735 q = 1) : d297666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39908, d297666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94109 q ha hb
    | true =>
      simp only [d39908, d297666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94078 q ha hb
  have h2 (q : Pattern) (ha : d281024 q = 1) (hb : d287735 q = 1) : d297667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281024, d297667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d281024, d297667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39914 q = 1) (hb : d287735 q = 1) : d297669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39914, d297669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94110 q ha hb
    | true =>
      simp only [d39914, d297669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39915 q = 1) (hb : d287735 q = 1) : d297670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39915, d297670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39915, d297670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d281025 q = 1) (hb : d287735 q = 1) : d297671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281025, d297671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281025, d297671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d281033 q = 1) (hb : d287735 q = 1) : d297692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281033, d297692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281033, d297692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d281034 q = 1) (hb : d287735 q = 1) : d297693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281034, d297693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281034, d297693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d281035 q = 1) (hb : d287735 q = 1) : d297694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281035, d297694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281035, d297694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94113 (p : Pattern) (ha : d30413 p = 1) (hb : d287735 p = 1) : d281910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30399 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94093 q ha hb
  have h2 (q : Pattern) (ha : d30199 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94093 q ha hb
    | true =>
      simp only [d30199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30400 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30200 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30401 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30402 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30403 q = 1) (hb : d287735 q = 1) : d32991 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30403, d32991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30403, d32991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94064 q ha hb
  have h8 (q : Pattern) (ha : d30088 q = 1) (hb : d287735 q = 1) : d32694 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d32694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94064 q ha hb
    | true =>
      simp only [d30088, d32694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30404 q = 1) (hb : d287735 q = 1) : d32992 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30404, d32992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30404, d32992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30089 q = 1) (hb : d287735 q = 1) : d32695 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d32695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30089, d32695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30405 q = 1) (hb : d287735 q = 1) : d32993 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30405, d32993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30405, d32993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30406 q = 1) (hb : d287735 q = 1) : d32994 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30406, d32994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30406, d32994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30407 q = 1) (hb : d287735 q = 1) : d32995 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30407, d32995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30407, d32995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30408 q = 1) (hb : d287735 q = 1) : d281905 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94066 q ha hb
  have h15 (q : Pattern) (ha : d30098 q = 1) (hb : d287735 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94066 q ha hb
    | true =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30409 q = 1) (hb : d287735 q = 1) : d281906 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30409, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30099 q = 1) (hb : d287735 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30410 q = 1) (hb : d287735 q = 1) : d281907 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30410, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30411 q = 1) (hb : d287735 q = 1) : d281908 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d30411, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d30412 q = 1) (hb : d287735 q = 1) : d281909 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30412, d281909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30412, d281909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d30413 q = 1) (hb : d287735 q = 1) : d281910 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30413, d281910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30413, d281910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro94114 (p : Pattern) (ha : d39952 p = 1) (hb : d287735 p = 1) : d297707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30403 q = 1) (hb : d287735 q = 1) : d32991 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30403, d32991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30403, d32991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94064 q ha hb
  have h2 (q : Pattern) (ha : d30088 q = 1) (hb : d287735 q = 1) : d32694 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d32694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94064 q ha hb
    | true =>
      simp only [d30088, d32694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30404 q = 1) (hb : d287735 q = 1) : d32992 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30404, d32992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30404, d32992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30089 q = 1) (hb : d287735 q = 1) : d32695 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d32695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30089, d32695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30405 q = 1) (hb : d287735 q = 1) : d32993 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30405, d32993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30405, d32993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30406 q = 1) (hb : d287735 q = 1) : d32994 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30406, d32994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30406, d32994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30408 q = 1) (hb : d287735 q = 1) : d281905 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94066 q ha hb
  have h8 (q : Pattern) (ha : d30098 q = 1) (hb : d287735 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94066 q ha hb
    | true =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30409 q = 1) (hb : d287735 q = 1) : d281906 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30409, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30099 q = 1) (hb : d287735 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30410 q = 1) (hb : d287735 q = 1) : d281907 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30410, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30411 q = 1) (hb : d287735 q = 1) : d281908 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30411, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30412 q = 1) (hb : d287735 q = 1) : d281909 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30412, d281909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30412, d281909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39947 q = 1) (hb : d287735 q = 1) : d297702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39947, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39947, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94067 q ha hb
  have h15 (q : Pattern) (ha : d39705 q = 1) (hb : d287735 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94067 q ha hb
    | true =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d39948 q = 1) (hb : d287735 q = 1) : d297703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39948, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d39948, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39706 q = 1) (hb : d287735 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d39949 q = 1) (hb : d287735 q = 1) : d297704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39949, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d39949, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d39950 q = 1) (hb : d287735 q = 1) : d297705 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39950, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d39950, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d39951 q = 1) (hb : d287735 q = 1) : d297706 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39951, d297706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39951, d297706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d39952 q = 1) (hb : d287735 q = 1) : d297707 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39952, d297707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39952, d297707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro94115 (p : Pattern) (ha : d39957 p = 1) (hb : d287735 p = 1) : d297712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30408 q = 1) (hb : d287735 q = 1) : d281905 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94066 q ha hb
  have h2 (q : Pattern) (ha : d30098 q = 1) (hb : d287735 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94066 q ha hb
    | true =>
      simp only [d30098, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30409 q = 1) (hb : d287735 q = 1) : d281906 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30409, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30099 q = 1) (hb : d287735 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30099, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30410 q = 1) (hb : d287735 q = 1) : d281907 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30410, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30411 q = 1) (hb : d287735 q = 1) : d281908 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30411, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39947 q = 1) (hb : d287735 q = 1) : d297702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39947, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39947, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94067 q ha hb
  have h8 (q : Pattern) (ha : d39705 q = 1) (hb : d287735 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94067 q ha hb
    | true =>
      simp only [d39705, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39948 q = 1) (hb : d287735 q = 1) : d297703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39948, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39948, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39706 q = 1) (hb : d287735 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39706, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39949 q = 1) (hb : d287735 q = 1) : d297704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39949, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39949, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d39950 q = 1) (hb : d287735 q = 1) : d297705 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39950, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d39950, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d39951 q = 1) (hb : d287735 q = 1) : d297706 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39951, d297706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39951, d297706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39956 q = 1) (hb : d287735 q = 1) : d297711 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39956, d297711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39956, d297711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39957 q = 1) (hb : d287735 q = 1) : d297712 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39957, d297712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39957, d297712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94116 (p : Pattern) (ha : d39982 p = 1) (hb : d287735 p = 1) : d297737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39953 q = 1) (hb : d287735 q = 1) : d297708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39953, d297708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94113 q ha hb
    | true =>
      simp only [d39953, d297708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94114 q ha hb
  have h2 (q : Pattern) (ha : d39954 q = 1) (hb : d287735 q = 1) : d297709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39954, d297709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39954, d297709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39955 q = 1) (hb : d287735 q = 1) : d297710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39955, d297710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39955, d297710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39958 q = 1) (hb : d287735 q = 1) : d297713 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39958, d297713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94114 q ha hb
    | true =>
      simp only [d39958, d297713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94115 q ha hb
  have h5 (q : Pattern) (ha : d39959 q = 1) (hb : d287735 q = 1) : d297714 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39959, d297714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39959, d297714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39960 q = 1) (hb : d287735 q = 1) : d297715 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39960, d297715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39960, d297715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39961 q = 1) (hb : d287735 q = 1) : d297716 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39961, d297716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39961, d297716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39972 q = 1) (hb : d287735 q = 1) : d297727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39972, d297727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94114 q ha hb
    | true =>
      simp only [d39972, d297727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94084 q ha hb
  have h9 (q : Pattern) (ha : d39973 q = 1) (hb : d287735 q = 1) : d297728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39973, d297728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39973, d297728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39974 q = 1) (hb : d287735 q = 1) : d297729 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39974, d297729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39974, d297729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39977 q = 1) (hb : d287735 q = 1) : d297732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39977, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94084 q ha hb
    | true =>
      simp only [d39977, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94085 q ha hb
  have h12 (q : Pattern) (ha : d39978 q = 1) (hb : d287735 q = 1) : d297733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39978, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39978, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39979 q = 1) (hb : d287735 q = 1) : d297734 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39979, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39979, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39980 q = 1) (hb : d287735 q = 1) : d297735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39980, d297735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39980, d297735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39981 q = 1) (hb : d287735 q = 1) : d297736 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39981, d297736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39981, d297736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d39982 q = 1) (hb : d287735 q = 1) : d297737 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39982, d297737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39982, d297737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro94117 (p : Pattern) (ha : d39987 p = 1) (hb : d287735 p = 1) : d297742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39972 q = 1) (hb : d287735 q = 1) : d297727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39972, d297727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94114 q ha hb
    | true =>
      simp only [d39972, d297727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94084 q ha hb
  have h2 (q : Pattern) (ha : d39973 q = 1) (hb : d287735 q = 1) : d297728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39973, d297728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39973, d297728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39974 q = 1) (hb : d287735 q = 1) : d297729 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39974, d297729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39974, d297729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39977 q = 1) (hb : d287735 q = 1) : d297732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39977, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94084 q ha hb
    | true =>
      simp only [d39977, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94085 q ha hb
  have h5 (q : Pattern) (ha : d39978 q = 1) (hb : d287735 q = 1) : d297733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39978, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39978, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39979 q = 1) (hb : d287735 q = 1) : d297734 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39979, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39979, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39980 q = 1) (hb : d287735 q = 1) : d297735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39980, d297735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39980, d297735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39985 q = 1) (hb : d287735 q = 1) : d297740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39985, d297740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39985, d297740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39986 q = 1) (hb : d287735 q = 1) : d297741 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39986, d297741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39986, d297741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39987 q = 1) (hb : d287735 q = 1) : d297742 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39987, d297742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39987, d297742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro94118 (p : Pattern) (ha : d39993 p = 1) (hb : d287735 p = 1) : d297748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39983 q = 1) (hb : d287735 q = 1) : d297738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39983, d297738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94116 q ha hb
    | true =>
      simp only [d39983, d297738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39984 q = 1) (hb : d287735 q = 1) : d297739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39984, d297739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39984, d297739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39988 q = 1) (hb : d287735 q = 1) : d297743 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39988, d297743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94117 q ha hb
    | true =>
      simp only [d39988, d297743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39989 q = 1) (hb : d287735 q = 1) : d297744 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39989, d297744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39989, d297744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39990 q = 1) (hb : d287735 q = 1) : d297745 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39990, d297745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39990, d297745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39991 q = 1) (hb : d287735 q = 1) : d297746 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39991, d297746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39991, d297746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39992 q = 1) (hb : d287735 q = 1) : d297747 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39992, d297747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39992, d297747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39993 q = 1) (hb : d287735 q = 1) : d297748 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39993, d297748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39993, d297748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94119 (p : Pattern) (ha : d40001 p = 1) (hb : d287735 p = 1) : d297756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39988 q = 1) (hb : d287735 q = 1) : d297743 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39988, d297743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94117 q ha hb
    | true =>
      simp only [d39988, d297743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39989 q = 1) (hb : d287735 q = 1) : d297744 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39989, d297744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39989, d297744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39996 q = 1) (hb : d287735 q = 1) : d297751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39996, d297751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94086 q ha hb
    | true =>
      simp only [d39996, d297751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39997 q = 1) (hb : d287735 q = 1) : d297752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39997, d297752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39997, d297752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39998 q = 1) (hb : d287735 q = 1) : d297753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39998, d297753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39998, d297753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39999 q = 1) (hb : d287735 q = 1) : d297754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39999, d297754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39999, d297754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40000 q = 1) (hb : d287735 q = 1) : d297755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40000, d297755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40000, d297755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40001 q = 1) (hb : d287735 q = 1) : d297756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40001, d297756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40001, d297756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94120 (p : Pattern) (ha : d40053 p = 1) (hb : d287735 p = 1) : d297764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39962 q = 1) (hb : d287735 q = 1) : d297717 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39962, d297717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39962, d297717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94069 q ha hb
  have h2 (q : Pattern) (ha : d39717 q = 1) (hb : d287735 q = 1) : d297527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94069 q ha hb
    | true =>
      simp only [d39717, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39963 q = 1) (hb : d287735 q = 1) : d297718 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39963, d297718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39963, d297718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39718 q = 1) (hb : d287735 q = 1) : d297528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39718, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39964 q = 1) (hb : d287735 q = 1) : d297719 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39964, d297719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39964, d297719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39965 q = 1) (hb : d287735 q = 1) : d297720 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39965, d297720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39965, d297720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39966 q = 1) (hb : d287735 q = 1) : d297721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39966, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39966, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94070 q ha hb
  have h8 (q : Pattern) (ha : d39722 q = 1) (hb : d287735 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94070 q ha hb
    | true =>
      simp only [d39722, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39967 q = 1) (hb : d287735 q = 1) : d297722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39967, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39967, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39723 q = 1) (hb : d287735 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39723, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39968 q = 1) (hb : d287735 q = 1) : d297723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39968, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39968, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d39969 q = 1) (hb : d287735 q = 1) : d297724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39969, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d39969, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d39970 q = 1) (hb : d287735 q = 1) : d297725 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39970, d297725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39970, d297725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40048 q = 1) (hb : d287735 q = 1) : d297759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40048, d297759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40048, d297759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94098 q ha hb
  have h15 (q : Pattern) (ha : d39862 q = 1) (hb : d287735 q = 1) : d297620 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39862, d297620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94098 q ha hb
    | true =>
      simp only [d39862, d297620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40049 q = 1) (hb : d287735 q = 1) : d297760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40049, d297760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40049, d297760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39863 q = 1) (hb : d287735 q = 1) : d297621 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39863, d297621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39863, d297621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40050 q = 1) (hb : d287735 q = 1) : d297761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40050, d297761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40050, d297761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40051 q = 1) (hb : d287735 q = 1) : d297762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40051, d297762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d40051, d297762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d40052 q = 1) (hb : d287735 q = 1) : d297763 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40052, d297763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d40052, d297763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d40053 q = 1) (hb : d287735 q = 1) : d297764 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40053, d297764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40053, d297764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro94121 (p : Pattern) (ha : d40059 p = 1) (hb : d287735 p = 1) : d297770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40054 q = 1) (hb : d287735 q = 1) : d297765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40054, d297765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40054, d297765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94100 q ha hb
  have h2 (q : Pattern) (ha : d39872 q = 1) (hb : d287735 q = 1) : d297630 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39872, d297630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94100 q ha hb
    | true =>
      simp only [d39872, d297630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40055 q = 1) (hb : d287735 q = 1) : d297766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40055, d297766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40055, d297766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39873 q = 1) (hb : d287735 q = 1) : d297631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39873, d297631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39873, d297631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40056 q = 1) (hb : d287735 q = 1) : d297767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40056, d297767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40056, d297767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40057 q = 1) (hb : d287735 q = 1) : d297768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40057, d297768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40057, d297768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40058 q = 1) (hb : d287735 q = 1) : d297769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40058, d297769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40058, d297769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40059 q = 1) (hb : d287735 q = 1) : d297770 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40059, d297770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40059, d297770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94122 (p : Pattern) (ha : d40065 p = 1) (hb : d287735 p = 1) : d297776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39972 q = 1) (hb : d287735 q = 1) : d297727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39972, d297727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94114 q ha hb
    | true =>
      simp only [d39972, d297727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94084 q ha hb
  have h2 (q : Pattern) (ha : d39973 q = 1) (hb : d287735 q = 1) : d297728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39973, d297728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39973, d297728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39974 q = 1) (hb : d287735 q = 1) : d297729 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39974, d297729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39974, d297729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39977 q = 1) (hb : d287735 q = 1) : d297732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39977, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94084 q ha hb
    | true =>
      simp only [d39977, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94085 q ha hb
  have h5 (q : Pattern) (ha : d39978 q = 1) (hb : d287735 q = 1) : d297733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39978, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39978, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39979 q = 1) (hb : d287735 q = 1) : d297734 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39979, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39979, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39980 q = 1) (hb : d287735 q = 1) : d297735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39980, d297735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39980, d297735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40060 q = 1) (hb : d287735 q = 1) : d297771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40060, d297771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94120 q ha hb
    | true =>
      simp only [d40060, d297771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94121 q ha hb
  have h9 (q : Pattern) (ha : d40061 q = 1) (hb : d287735 q = 1) : d297772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40061, d297772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40061, d297772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40062 q = 1) (hb : d287735 q = 1) : d297773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40062, d297773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40062, d297773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40063 q = 1) (hb : d287735 q = 1) : d297774 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40063, d297774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40063, d297774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40064 q = 1) (hb : d287735 q = 1) : d297775 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40064, d297775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40064, d297775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40065 q = 1) (hb : d287735 q = 1) : d297776 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40065, d297776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40065, d297776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro94123 (p : Pattern) (ha : d40071 p = 1) (hb : d287735 p = 1) : d297782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40066 q = 1) (hb : d287735 q = 1) : d297777 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40066, d297777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94122 q ha hb
    | true =>
      simp only [d40066, d297777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40067 q = 1) (hb : d287735 q = 1) : d297778 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40067, d297778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40067, d297778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40068 q = 1) (hb : d287735 q = 1) : d297779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40068, d297779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40068, d297779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40069 q = 1) (hb : d287735 q = 1) : d297780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40069, d297780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40069, d297780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40070 q = 1) (hb : d287735 q = 1) : d297781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40070, d297781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40070, d297781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40071 q = 1) (hb : d287735 q = 1) : d297782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40071, d297782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40071, d297782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94124 (p : Pattern) (ha : d281045 p = 1) (hb : d287735 p = 1) : d297788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40002 q = 1) (hb : d287735 q = 1) : d297757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40002, d297757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94118 q ha hb
    | true =>
      simp only [d40002, d297757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94119 q ha hb
  have h2 (q : Pattern) (ha : d281041 q = 1) (hb : d287735 q = 1) : d297758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281041, d297758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d281041, d297758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40072 q = 1) (hb : d287735 q = 1) : d297783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40072, d297783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94123 q ha hb
    | true =>
      simp only [d40072, d297783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40073 q = 1) (hb : d287735 q = 1) : d297784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40073, d297784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40073, d297784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d281042 q = 1) (hb : d287735 q = 1) : d297785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281042, d297785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281042, d297785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d281043 q = 1) (hb : d287735 q = 1) : d297786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281043, d297786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281043, d297786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d281044 q = 1) (hb : d287735 q = 1) : d297787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281044, d297787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281044, d297787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d281045 q = 1) (hb : d287735 q = 1) : d297788 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281045, d297788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281045, d297788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94125 (p : Pattern) (ha : d281051 p = 1) (hb : d287735 p = 1) : d297805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39761 q = 1) (hb : d287735 q = 1) : d297571 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39761, d297571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39761, d297571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94077 q ha hb
  have h2 (q : Pattern) (ha : d39762 q = 1) (hb : d287735 q = 1) : d297572 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39762, d297572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39762, d297572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39771 q = 1) (hb : d287735 q = 1) : d297581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39771, d297581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94077 q ha hb
    | true =>
      simp only [d39771, d297581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94080 q ha hb
  have h4 (q : Pattern) (ha : d39772 q = 1) (hb : d287735 q = 1) : d297582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39772, d297582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39772, d297582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39773 q = 1) (hb : d287735 q = 1) : d297583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d39773, d297583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39773, d297583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d281029 q = 1) (hb : d287735 q = 1) : d297675 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d281029, d297675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94104 q ha hb
    | true =>
      simp only [d281029, d297675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94111 q ha hb
  have h7 (q : Pattern) (ha : d39933 q = 1) (hb : d287735 q = 1) : d297688 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39933, d297688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94081 q ha hb
    | true =>
      simp only [d39933, d297688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94082 q ha hb
  have h8 (q : Pattern) (ha : d281030 q = 1) (hb : d287735 q = 1) : d297689 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d281030, d297689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d281030, d297689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d281031 q = 1) (hb : d287735 q = 1) : d297690 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d281031, d297690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d281031, d297690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d281032 q = 1) (hb : d287735 q = 1) : d297691 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d281032, d297691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d281032, d297691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d281036 q = 1) (hb : d287735 q = 1) : d297695 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d281036, d297695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281036, d297695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94112 q ha hb
  have h12 (q : Pattern) (ha : d39942 q = 1) (hb : d287735 q = 1) : d297697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39942, d297697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39942, d297697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94083 q ha hb
  have h13 (q : Pattern) (ha : d281037 q = 1) (hb : d287735 q = 1) : d297698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d281037, d297698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d281037, d297698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d281038 q = 1) (hb : d287735 q = 1) : d297699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d281038, d297699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d281038, d297699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d281039 q = 1) (hb : d287735 q = 1) : d297700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d281039, d297700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d281039, d297700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d281040 q = 1) (hb : d287735 q = 1) : d297701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d281040, d297701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d281040, d297701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d281046 q = 1) (hb : d287735 q = 1) : d297789 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d281046, d297789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281046, d297789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94124 q ha hb
  have h18 (q : Pattern) (ha : d40089 q = 1) (hb : d287735 q = 1) : d297800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40089, d297800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40089, d297800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94088 q ha hb
  have h19 (q : Pattern) (ha : d281047 q = 1) (hb : d287735 q = 1) : d297801 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d281047, d297801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d281047, d297801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d281048 q = 1) (hb : d287735 q = 1) : d297802 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d281048, d297802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d281048, d297802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d281049 q = 1) (hb : d287735 q = 1) : d297803 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d281049, d297803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d281049, d297803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d281050 q = 1) (hb : d287735 q = 1) : d297804 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d281050, d297804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d281050, d297804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d281051 q = 1) (hb : d287735 q = 1) : d297805 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d281051, d297805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d281051, d297805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro94126 (p : Pattern) (ha : d281057 p = 1) (hb : d287735 p = 1) : d297811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d281052 q = 1) (hb : d287735 q = 1) : d297806 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d281052, d297806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281052, d297806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94125 q ha hb
  have h2 (q : Pattern) (ha : d281053 q = 1) (hb : d287735 q = 1) : d297807 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d281053, d297807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281053, d297807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281054 q = 1) (hb : d287735 q = 1) : d297808 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d281054, d297808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281054, d297808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281055 q = 1) (hb : d287735 q = 1) : d297809 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d281055, d297809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281055, d297809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d281056 q = 1) (hb : d287735 q = 1) : d297810 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d281056, d297810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281056, d297810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d281057 q = 1) (hb : d287735 q = 1) : d297811 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d281057, d297811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281057, d297811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94127 (p : Pattern) (ha : d40151 p = 1) (hb : d287735 p = 1) : d296090 p = 1 := by
  have h0 (q : Pattern) (ha : d40150 q = 1) (hb : d253269 q = 1) : d40150 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40151 q = 1) (hb : d287735 q = 1) : d296090 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d40151, d287735, d296090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40151, d287735, d296090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro94128 (p : Pattern) (ha : d40157 p = 1) (hb : d287735 p = 1) : d296096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40152 q = 1) (hb : d287735 q = 1) : d296091 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94127 q ha hb
    | true =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40153 q = 1) (hb : d287735 q = 1) : d296092 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d287735 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40154 q = 1) (hb : d287735 q = 1) : d296093 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d287735 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40155 q = 1) (hb : d287735 q = 1) : d296094 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40155, d296094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40155, d296094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40156 q = 1) (hb : d287735 q = 1) : d296095 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40156, d296095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40156, d296095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d287735 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d40157 q = 1) (hb : d287735 q = 1) : d296096 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40157, d296096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40157, d296096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro94129 (p : Pattern) (ha : d40163 p = 1) (hb : d287735 p = 1) : d296102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40158 q = 1) (hb : d287735 q = 1) : d296097 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40158, d296097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94128 q ha hb
    | true =>
      simp only [d40158, d296097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40159 q = 1) (hb : d287735 q = 1) : d296098 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40159, d296098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40159, d296098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40160 q = 1) (hb : d287735 q = 1) : d296099 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40160, d296099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40160, d296099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40161 q = 1) (hb : d287735 q = 1) : d296100 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40161, d296100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40161, d296100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d287735 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40162 q = 1) (hb : d287735 q = 1) : d296101 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40162, d296101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40162, d296101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d287735 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d40163 q = 1) (hb : d287735 q = 1) : d296102 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40163, d296102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40163, d296102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94130 (p : Pattern) (ha : d40169 p = 1) (hb : d287735 p = 1) : d296108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d287735 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40164 q = 1) (hb : d287735 q = 1) : d296103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40164, d296103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94129 q ha hb
    | true =>
      simp only [d40164, d296103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40165 q = 1) (hb : d287735 q = 1) : d296104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40165, d296104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40165, d296104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40166 q = 1) (hb : d287735 q = 1) : d296105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40166, d296105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40166, d296105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d287735 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40167 q = 1) (hb : d287735 q = 1) : d296106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40167, d296106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40167, d296106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d287735 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d40168 q = 1) (hb : d287735 q = 1) : d296107 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40168, d296107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40168, d296107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40169 q = 1) (hb : d287735 q = 1) : d296108 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40169, d296108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40169, d296108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro94131 (p : Pattern) (ha : d40175 p = 1) (hb : d287735 p = 1) : d296114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d287735 q = 1) : d296109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94130 q ha hb
    | true =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d287735 q = 1) : d296110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287735 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40172 q = 1) (hb : d287735 q = 1) : d296111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40173 q = 1) (hb : d287735 q = 1) : d296112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40173, d296112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40173, d296112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40174 q = 1) (hb : d287735 q = 1) : d296113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40174, d296113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40174, d296113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40175 q = 1) (hb : d287735 q = 1) : d296114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40175, d296114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40175, d296114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro94132 (p : Pattern) (ha : d287735 p = 1) (hb : d289282 p = 1) : d296120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d287735 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d287735 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d287735 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40176 q = 1) (hb : d287735 q = 1) : d296115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d296115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94131 q ha hb
    | true =>
      simp only [d40176, d296115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289278 q = 1) : d296116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289278, d296116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289278, d296116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d287735 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d287735 q = 1) (hb : d289279 q = 1) : d296117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289279, d296117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289279, d296117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289280 q = 1) : d296118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289280, d296118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289280, d296118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287735 q = 1) (hb : d289281 q = 1) : d296119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289281, d296119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289281, d296119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287735 q = 1) (hb : d289282 q = 1) : d296120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289282, d296120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289282, d296120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro94133 (p : Pattern) (ha : d40182 p = 1) (hb : d287735 p = 1) : d296121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d287735 q = 1) : d296109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94130 q ha hb
    | true =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d287735 q = 1) : d296110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287735 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40172 q = 1) (hb : d287735 q = 1) : d296111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40173 q = 1) (hb : d287735 q = 1) : d296112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40173, d296112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40173, d296112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40174 q = 1) (hb : d287735 q = 1) : d296113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40174, d296113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40174, d296113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40182 q = 1) (hb : d287735 q = 1) : d296121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40182, d296121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40182, d296121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro94134 (p : Pattern) (ha : d287735 p = 1) (hb : d289287 p = 1) : d296127 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d287735 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d287735 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d287735 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40176 q = 1) (hb : d287735 q = 1) : d296115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d296115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94131 q ha hb
    | true =>
      simp only [d40176, d296115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289278 q = 1) : d296116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289278, d296116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d289278, d296116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d287735 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d287735 q = 1) (hb : d289279 q = 1) : d296117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289279, d296117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289279, d296117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289280 q = 1) : d296118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289280, d296118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289280, d296118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287735 q = 1) (hb : d289281 q = 1) : d296119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289281, d296119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289281, d296119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d287735 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d287735 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d287735 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d40183 q = 1) (hb : d287735 q = 1) : d296122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40183, d296122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94133 q ha hb
    | true =>
      simp only [d40183, d296122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d287735 q = 1) (hb : d289283 q = 1) : d296123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289283, d296123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d289283, d296123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d287735 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d287735 q = 1) (hb : d289284 q = 1) : d296124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289284, d296124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289284, d296124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d287735 q = 1) (hb : d289285 q = 1) : d296125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289285, d296125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d289285, d296125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d287735 q = 1) (hb : d289286 q = 1) : d296126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289286, d296126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d289286, d296126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d287735 q = 1) (hb : d289287 q = 1) : d296127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289287, d296127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289287, d296127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro94135 (p : Pattern) (ha : d287735 p = 1) (hb : d289294 p = 1) : d296134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d287735 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40183 q = 1) (hb : d287735 q = 1) : d296122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40183, d296122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94133 q ha hb
    | true =>
      simp only [d40183, d296122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287735 q = 1) (hb : d289283 q = 1) : d296123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289283, d296123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289283, d296123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d287735 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289284 q = 1) : d296124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289284, d296124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289284, d296124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289292 q = 1) : d296132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289292, d296132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289292, d296132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287735 q = 1) (hb : d289293 q = 1) : d296133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289293, d296133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289293, d296133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289294 q = 1) : d296134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289294, d296134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289294, d296134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94136 (p : Pattern) (ha : d40206 p = 1) (hb : d287735 p = 1) : d296145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40201 q = 1) (hb : d287735 q = 1) : d296140 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40201, d296140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40201, d296140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94128 q ha hb
  have h2 (q : Pattern) (ha : d40158 q = 1) (hb : d287735 q = 1) : d296097 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40158, d296097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94128 q ha hb
    | true =>
      simp only [d40158, d296097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40202 q = 1) (hb : d287735 q = 1) : d296141 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40202, d296141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40202, d296141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40159 q = 1) (hb : d287735 q = 1) : d296098 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40159, d296098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40159, d296098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40203 q = 1) (hb : d287735 q = 1) : d296142 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40203, d296142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40203, d296142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40204 q = 1) (hb : d287735 q = 1) : d296143 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40204, d296143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40204, d296143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d287735 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d40205 q = 1) (hb : d287735 q = 1) : d296144 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40205, d296144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40205, d296144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d287735 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d40206 q = 1) (hb : d287735 q = 1) : d296145 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40206, d296145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40206, d296145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro94137 (p : Pattern) (ha : d40212 p = 1) (hb : d287735 p = 1) : d296151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d287735 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40207 q = 1) (hb : d287735 q = 1) : d296146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40207, d296146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94136 q ha hb
    | true =>
      simp only [d40207, d296146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40208 q = 1) (hb : d287735 q = 1) : d296147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40208, d296147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40208, d296147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40209 q = 1) (hb : d287735 q = 1) : d296148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40209, d296148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40209, d296148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d287735 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40210 q = 1) (hb : d287735 q = 1) : d296149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40210, d296149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40210, d296149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d287735 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d40211 q = 1) (hb : d287735 q = 1) : d296150 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40211, d296150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40211, d296150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40212 q = 1) (hb : d287735 q = 1) : d296151 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40212, d296151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40212, d296151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro94138 (p : Pattern) (ha : d40218 p = 1) (hb : d287735 p = 1) : d296157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40213 q = 1) (hb : d287735 q = 1) : d296152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40213, d296152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94137 q ha hb
    | true =>
      simp only [d40213, d296152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40214 q = 1) (hb : d287735 q = 1) : d296153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40214, d296153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40214, d296153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d287735 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40215 q = 1) (hb : d287735 q = 1) : d296154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40215, d296154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40215, d296154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40216 q = 1) (hb : d287735 q = 1) : d296155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40216, d296155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40216, d296155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40217 q = 1) (hb : d287735 q = 1) : d296156 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40217, d296156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40217, d296156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40218 q = 1) (hb : d287735 q = 1) : d296157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40218, d296157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40218, d296157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro94139 (p : Pattern) (ha : d287735 p = 1) (hb : d289304 p = 1) : d296163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d287735 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40219 q = 1) (hb : d287735 q = 1) : d296158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40219, d296158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94138 q ha hb
    | true =>
      simp only [d40219, d296158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287735 q = 1) (hb : d289300 q = 1) : d296159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289300, d296159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289300, d296159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d287735 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289301 q = 1) : d296160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289301, d296160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289301, d296160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289302 q = 1) : d296161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289302, d296161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289302, d296161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287735 q = 1) (hb : d289303 q = 1) : d296162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289303, d296162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289303, d296162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289304 q = 1) : d296163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289304, d296163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289304, d296163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94140 (p : Pattern) (ha : d287735 p = 1) (hb : d289310 p = 1) : d296169 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d287735 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287735 q = 1) (hb : d289288 q = 1) : d296128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289288, d296128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94132 q ha hb
    | true =>
      simp only [d289288, d296128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94134 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d287735 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287735 q = 1) (hb : d289289 q = 1) : d296129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289289, d296129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289289, d296129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289290 q = 1) : d296130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289290, d296130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289290, d296130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289291 q = 1) : d296131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289291, d296131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289291, d296131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287735 q = 1) (hb : d289295 q = 1) : d296135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289295, d296135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289295, d296135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94135 q ha hb
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289296 q = 1) : d296136 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289296, d296136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289296, d296136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d287735 q = 1) (hb : d289297 q = 1) : d296137 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289297, d296137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289297, d296137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d287735 q = 1) (hb : d289298 q = 1) : d296138 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289298, d296138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289298, d296138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d287735 q = 1) (hb : d289299 q = 1) : d296139 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289299, d296139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289299, d296139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d287735 q = 1) (hb : d289305 q = 1) : d296164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289305, d296164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289305, d296164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94139 q ha hb
  have h13 (q : Pattern) (ha : d287735 q = 1) (hb : d289306 q = 1) : d296165 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289306, d296165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289306, d296165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d287735 q = 1) (hb : d289307 q = 1) : d296166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289307, d296166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289307, d296166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d287735 q = 1) (hb : d289308 q = 1) : d296167 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289308, d296167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289308, d296167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d287735 q = 1) (hb : d289309 q = 1) : d296168 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289309, d296168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289309, d296168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d287735 q = 1) (hb : d289310 q = 1) : d296169 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289310, d296169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289310, d296169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro94141 (p : Pattern) (ha : d40240 p = 1) (hb : d287735 p = 1) : d296179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d287735 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40176 q = 1) (hb : d287735 q = 1) : d296115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d296115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94131 q ha hb
    | true =>
      simp only [d40176, d296115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40236 q = 1) (hb : d287735 q = 1) : d296175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40236, d296175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40236, d296175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40237 q = 1) (hb : d287735 q = 1) : d296176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40237, d296176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40237, d296176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40238 q = 1) (hb : d287735 q = 1) : d296177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40238, d296177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40238, d296177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40239 q = 1) (hb : d287735 q = 1) : d296178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40239, d296178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40239, d296178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40240 q = 1) (hb : d287735 q = 1) : d296179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40240, d296179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40240, d296179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro94142 (p : Pattern) (ha : d40247 p = 1) (hb : d287735 p = 1) : d296186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d287735 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40176 q = 1) (hb : d287735 q = 1) : d296115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d296115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94131 q ha hb
    | true =>
      simp only [d40176, d296115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40236 q = 1) (hb : d287735 q = 1) : d296175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40236, d296175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40236, d296175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40237 q = 1) (hb : d287735 q = 1) : d296176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40237, d296176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40237, d296176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40238 q = 1) (hb : d287735 q = 1) : d296177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40238, d296177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40238, d296177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40239 q = 1) (hb : d287735 q = 1) : d296178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40239, d296178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40239, d296178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d287735 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d40183 q = 1) (hb : d287735 q = 1) : d296122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40183, d296122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94133 q ha hb
    | true =>
      simp only [d40183, d296122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40243 q = 1) (hb : d287735 q = 1) : d296182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40243, d296182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40243, d296182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40244 q = 1) (hb : d287735 q = 1) : d296183 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40244, d296183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40244, d296183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40245 q = 1) (hb : d287735 q = 1) : d296184 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40245, d296184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40245, d296184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40246 q = 1) (hb : d287735 q = 1) : d296185 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40246, d296185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40246, d296185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40247 q = 1) (hb : d287735 q = 1) : d296186 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40247, d296186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40247, d296186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro94143 (p : Pattern) (ha : d40359 p = 1) (hb : d287735 p = 1) : d296267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d287735 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40176 q = 1) (hb : d287735 q = 1) : d296115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d296115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94131 q ha hb
    | true =>
      simp only [d40176, d296115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40236 q = 1) (hb : d287735 q = 1) : d296175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40236, d296175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40236, d296175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40237 q = 1) (hb : d287735 q = 1) : d296176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40237, d296176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40237, d296176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40238 q = 1) (hb : d287735 q = 1) : d296177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40238, d296177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40238, d296177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40239 q = 1) (hb : d287735 q = 1) : d296178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40239, d296178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40239, d296178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d287735 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d40359 q = 1) (hb : d287735 q = 1) : d296267 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40359, d296267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40359, d296267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94144 (p : Pattern) (ha : d40252 p = 1) (hb : d287735 p = 1) : d296191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d287735 q = 1) : d296109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94130 q ha hb
    | true =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d287735 q = 1) : d296110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287735 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40172 q = 1) (hb : d287735 q = 1) : d296111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40173 q = 1) (hb : d287735 q = 1) : d296112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40173, d296112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40173, d296112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40251 q = 1) (hb : d287735 q = 1) : d296190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40251, d296190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40251, d296190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40252 q = 1) (hb : d287735 q = 1) : d296191 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40252, d296191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40252, d296191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro94145 (p : Pattern) (ha : d40259 p = 1) (hb : d287735 p = 1) : d296198 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d287735 q = 1) : d296109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94130 q ha hb
    | true =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d287735 q = 1) : d296110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287735 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40172 q = 1) (hb : d287735 q = 1) : d296111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40257 q = 1) (hb : d287735 q = 1) : d296196 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40257, d296196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40257, d296196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40258 q = 1) (hb : d287735 q = 1) : d296197 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40258, d296197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40258, d296197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40259 q = 1) (hb : d287735 q = 1) : d296198 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40259, d296198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40259, d296198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro94146 (p : Pattern) (ha : d40264 p = 1) (hb : d287735 p = 1) : d296202 p = 1 := by
  have h0 (q : Pattern) (ha : d40263 q = 1) (hb : d253269 q = 1) : d40263 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40264 q = 1) (hb : d287735 q = 1) : d296202 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d40264, d287735, d296202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40264, d287735, d296202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro94147 (p : Pattern) (ha : d40270 p = 1) (hb : d287735 p = 1) : d296208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40265 q = 1) (hb : d287735 q = 1) : d296203 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94146 q ha hb
    | true =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40266 q = 1) (hb : d287735 q = 1) : d296204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40152 q = 1) (hb : d287735 q = 1) : d296091 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94127 q ha hb
    | true =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40153 q = 1) (hb : d287735 q = 1) : d296092 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40267 q = 1) (hb : d287735 q = 1) : d296205 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d287735 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40154 q = 1) (hb : d287735 q = 1) : d296093 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40268 q = 1) (hb : d287735 q = 1) : d296206 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40268, d296206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40268, d296206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40269 q = 1) (hb : d287735 q = 1) : d296207 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40269, d296207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40269, d296207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d287735 q = 1) : d21 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d40155 q = 1) (hb : d287735 q = 1) : d296094 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40155, d296094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40155, d296094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40156 q = 1) (hb : d287735 q = 1) : d296095 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40156, d296095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40156, d296095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40270 q = 1) (hb : d287735 q = 1) : d296208 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40270, d296208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40270, d296208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro94148 (p : Pattern) (ha : d40278 p = 1) (hb : d287735 p = 1) : d296216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40152 q = 1) (hb : d287735 q = 1) : d296091 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94127 q ha hb
    | true =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40153 q = 1) (hb : d287735 q = 1) : d296092 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d287735 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40154 q = 1) (hb : d287735 q = 1) : d296093 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40276 q = 1) (hb : d287735 q = 1) : d296214 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40276, d296214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40276, d296214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40277 q = 1) (hb : d287735 q = 1) : d296215 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40277, d296215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40277, d296215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d287735 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d40278 q = 1) (hb : d287735 q = 1) : d296216 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40278, d296216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40278, d296216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94149 (p : Pattern) (ha : d40284 p = 1) (hb : d287735 p = 1) : d296222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40271 q = 1) (hb : d287735 q = 1) : d296209 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40271, d296209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94147 q ha hb
    | true =>
      simp only [d40271, d296209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40272 q = 1) (hb : d287735 q = 1) : d296210 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40272, d296210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40272, d296210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40273 q = 1) (hb : d287735 q = 1) : d296211 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40273, d296211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40273, d296211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40274 q = 1) (hb : d287735 q = 1) : d296212 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40274, d296212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40274, d296212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40158 q = 1) (hb : d287735 q = 1) : d296097 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40158, d296097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94128 q ha hb
    | true =>
      simp only [d40158, d296097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40159 q = 1) (hb : d287735 q = 1) : d296098 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40159, d296098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40159, d296098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40160 q = 1) (hb : d287735 q = 1) : d296099 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40160, d296099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40160, d296099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40161 q = 1) (hb : d287735 q = 1) : d296100 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40161, d296100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40161, d296100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40275 q = 1) (hb : d287735 q = 1) : d296213 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40275, d296213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40275, d296213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40279 q = 1) (hb : d287735 q = 1) : d296217 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94148 q ha hb
    | true =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40280 q = 1) (hb : d287735 q = 1) : d296218 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40281 q = 1) (hb : d287735 q = 1) : d296219 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40281, d296219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40281, d296219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40282 q = 1) (hb : d287735 q = 1) : d296220 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40282, d296220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40282, d296220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d287735 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d40283 q = 1) (hb : d287735 q = 1) : d296221 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40283, d296221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40283, d296221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40284 q = 1) (hb : d287735 q = 1) : d296222 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40284, d296222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40284, d296222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro94150 (p : Pattern) (ha : d40290 p = 1) (hb : d287735 p = 1) : d296228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40285 q = 1) (hb : d287735 q = 1) : d296223 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40285, d296223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94149 q ha hb
    | true =>
      simp only [d40285, d296223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94129 q ha hb
  have h2 (q : Pattern) (ha : d40286 q = 1) (hb : d287735 q = 1) : d296224 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40286, d296224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40286, d296224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40287 q = 1) (hb : d287735 q = 1) : d296225 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40287, d296225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40287, d296225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d287735 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40164 q = 1) (hb : d287735 q = 1) : d296103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40164, d296103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94129 q ha hb
    | true =>
      simp only [d40164, d296103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40165 q = 1) (hb : d287735 q = 1) : d296104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40165, d296104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40165, d296104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40166 q = 1) (hb : d287735 q = 1) : d296105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40166, d296105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40166, d296105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40288 q = 1) (hb : d287735 q = 1) : d296226 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40288, d296226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40288, d296226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d287735 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d40167 q = 1) (hb : d287735 q = 1) : d296106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40167, d296106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40167, d296106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40289 q = 1) (hb : d287735 q = 1) : d296227 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40289, d296227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40289, d296227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40290 q = 1) (hb : d287735 q = 1) : d296228 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40290, d296228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40290, d296228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro94151 (p : Pattern) (ha : d40296 p = 1) (hb : d287735 p = 1) : d296234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40291 q = 1) (hb : d287735 q = 1) : d296229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40291, d296229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94150 q ha hb
    | true =>
      simp only [d40291, d296229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40292 q = 1) (hb : d287735 q = 1) : d296230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40292, d296230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40292, d296230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40170 q = 1) (hb : d287735 q = 1) : d296109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94130 q ha hb
    | true =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40171 q = 1) (hb : d287735 q = 1) : d296110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40293 q = 1) (hb : d287735 q = 1) : d296231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40293, d296231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40293, d296231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40294 q = 1) (hb : d287735 q = 1) : d296232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40294, d296232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40294, d296232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40295 q = 1) (hb : d287735 q = 1) : d296233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40295, d296233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40295, d296233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40296 q = 1) (hb : d287735 q = 1) : d296234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40296, d296234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40296, d296234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94152 (p : Pattern) (ha : d40330 p = 1) (hb : d287735 p = 1) : d296240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d287735 q = 1) : d296109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94130 q ha hb
    | true =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d287735 q = 1) : d296110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40327 q = 1) (hb : d287735 q = 1) : d296237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40327, d296237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40327, d296237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40328 q = 1) (hb : d287735 q = 1) : d296238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40328, d296238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40328, d296238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40329 q = 1) (hb : d287735 q = 1) : d296239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40329, d296239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40329, d296239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40330 q = 1) (hb : d287735 q = 1) : d296240 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40330, d296240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40330, d296240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94153 (p : Pattern) (ha : d287735 p = 1) (hb : d289320 p = 1) : d296246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d287735 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40253 q = 1) (hb : d287735 q = 1) : d296192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40253, d296192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94144 q ha hb
    | true =>
      simp only [d40253, d296192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40254 q = 1) (hb : d287735 q = 1) : d296193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40254, d296193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40254, d296193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40255 q = 1) (hb : d287735 q = 1) : d296194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40255, d296194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40255, d296194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40256 q = 1) (hb : d287735 q = 1) : d296195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40256, d296195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40256, d296195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d287735 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40260 q = 1) (hb : d287735 q = 1) : d296199 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40260, d296199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94145 q ha hb
    | true =>
      simp only [d40260, d296199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40261 q = 1) (hb : d287735 q = 1) : d296200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40261, d296200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40261, d296200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40262 q = 1) (hb : d287735 q = 1) : d296201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40262, d296201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40262, d296201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40297 q = 1) (hb : d287735 q = 1) : d296235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40297, d296235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94151 q ha hb
    | true =>
      simp only [d40297, d296235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94131 q ha hb
  have h11 (q : Pattern) (ha : d287735 q = 1) (hb : d289316 q = 1) : d296236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289316, d296236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d289316, d296236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d40331 q = 1) (hb : d287735 q = 1) : d296241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40331, d296241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94152 q ha hb
    | true =>
      simp only [d40331, d296241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40332 q = 1) (hb : d287735 q = 1) : d296242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40332, d296242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40332, d296242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d287735 q = 1) (hb : d289317 q = 1) : d296243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289317, d296243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289317, d296243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d287735 q = 1) (hb : d289318 q = 1) : d296244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289318, d296244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d289318, d296244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d287735 q = 1) (hb : d289319 q = 1) : d296245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289319, d296245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d289319, d296245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d287735 q = 1) (hb : d289320 q = 1) : d296246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289320, d296246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289320, d296246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro94154 (p : Pattern) (ha : d40337 p = 1) (hb : d287735 p = 1) : d296247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d287735 q = 1) : d296109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94130 q ha hb
    | true =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d287735 q = 1) : d296110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287735 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40172 q = 1) (hb : d287735 q = 1) : d296111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40173 q = 1) (hb : d287735 q = 1) : d296112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40173, d296112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40173, d296112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40251 q = 1) (hb : d287735 q = 1) : d296190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40251, d296190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40251, d296190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40337 q = 1) (hb : d287735 q = 1) : d296247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40337, d296247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40337, d296247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro94155 (p : Pattern) (ha : d40342 p = 1) (hb : d287735 p = 1) : d296252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d287735 q = 1) : d296109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94130 q ha hb
    | true =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d287735 q = 1) : d296110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287735 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40172 q = 1) (hb : d287735 q = 1) : d296111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d296111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40257 q = 1) (hb : d287735 q = 1) : d296196 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40257, d296196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40257, d296196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40258 q = 1) (hb : d287735 q = 1) : d296197 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40258, d296197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40258, d296197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40342 q = 1) (hb : d287735 q = 1) : d296252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40342, d296252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40342, d296252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro94156 (p : Pattern) (ha : d40346 p = 1) (hb : d287735 p = 1) : d296256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40291 q = 1) (hb : d287735 q = 1) : d296229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40291, d296229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94150 q ha hb
    | true =>
      simp only [d40291, d296229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40292 q = 1) (hb : d287735 q = 1) : d296230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40292, d296230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40292, d296230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40170 q = 1) (hb : d287735 q = 1) : d296109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94130 q ha hb
    | true =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40171 q = 1) (hb : d287735 q = 1) : d296110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40293 q = 1) (hb : d287735 q = 1) : d296231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40293, d296231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40293, d296231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40294 q = 1) (hb : d287735 q = 1) : d296232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40294, d296232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40294, d296232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40295 q = 1) (hb : d287735 q = 1) : d296233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40295, d296233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40295, d296233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40346 q = 1) (hb : d287735 q = 1) : d296256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40346, d296256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40346, d296256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94157 (p : Pattern) (ha : d40351 p = 1) (hb : d287735 p = 1) : d296259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d287735 q = 1) : d296109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94130 q ha hb
    | true =>
      simp only [d40170, d296109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d287735 q = 1) : d296110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d296110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40327 q = 1) (hb : d287735 q = 1) : d296237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40327, d296237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40327, d296237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40328 q = 1) (hb : d287735 q = 1) : d296238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40328, d296238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40328, d296238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40329 q = 1) (hb : d287735 q = 1) : d296239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40329, d296239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40329, d296239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40351 q = 1) (hb : d287735 q = 1) : d296259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40351, d296259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40351, d296259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94158 (p : Pattern) (ha : d287735 p = 1) (hb : d289325 p = 1) : d296265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d287735 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40253 q = 1) (hb : d287735 q = 1) : d296192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40253, d296192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94144 q ha hb
    | true =>
      simp only [d40253, d296192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40254 q = 1) (hb : d287735 q = 1) : d296193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40254, d296193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40254, d296193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40255 q = 1) (hb : d287735 q = 1) : d296194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40255, d296194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40255, d296194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40256 q = 1) (hb : d287735 q = 1) : d296195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40256, d296195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40256, d296195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d287735 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40260 q = 1) (hb : d287735 q = 1) : d296199 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40260, d296199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94145 q ha hb
    | true =>
      simp only [d40260, d296199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40261 q = 1) (hb : d287735 q = 1) : d296200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40261, d296200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40261, d296200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40262 q = 1) (hb : d287735 q = 1) : d296201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40262, d296201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40262, d296201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40297 q = 1) (hb : d287735 q = 1) : d296235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40297, d296235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94151 q ha hb
    | true =>
      simp only [d40297, d296235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94131 q ha hb
  have h11 (q : Pattern) (ha : d287735 q = 1) (hb : d289316 q = 1) : d296236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289316, d296236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d289316, d296236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d40331 q = 1) (hb : d287735 q = 1) : d296241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40331, d296241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94152 q ha hb
    | true =>
      simp only [d40331, d296241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40332 q = 1) (hb : d287735 q = 1) : d296242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40332, d296242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40332, d296242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d287735 q = 1) (hb : d289317 q = 1) : d296243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289317, d296243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289317, d296243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d287735 q = 1) (hb : d289318 q = 1) : d296244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289318, d296244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d289318, d296244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d287735 q = 1) (hb : d289319 q = 1) : d296245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289319, d296245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d289319, d296245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d287735 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d40338 q = 1) (hb : d287735 q = 1) : d296248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40338, d296248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94154 q ha hb
    | true =>
      simp only [d40338, d296248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40339 q = 1) (hb : d287735 q = 1) : d296249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40339, d296249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40339, d296249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d40340 q = 1) (hb : d287735 q = 1) : d296250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40340, d296250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d40340, d296250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d40341 q = 1) (hb : d287735 q = 1) : d296251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40341, d296251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40341, d296251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d287735 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d40343 q = 1) (hb : d287735 q = 1) : d296253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40343, d296253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94155 q ha hb
    | true =>
      simp only [d40343, d296253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d40344 q = 1) (hb : d287735 q = 1) : d296254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40344, d296254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40344, d296254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d40345 q = 1) (hb : d287735 q = 1) : d296255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40345, d296255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d40345, d296255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d40347 q = 1) (hb : d287735 q = 1) : d296257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40347, d296257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94156 q ha hb
    | true =>
      simp only [d40347, d296257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94133 q ha hb
  have h27 (q : Pattern) (ha : d287735 q = 1) (hb : d289321 q = 1) : d296258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289321, d296258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d289321, d296258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d40352 q = 1) (hb : d287735 q = 1) : d296260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40352, d296260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94157 q ha hb
    | true =>
      simp only [d40352, d296260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d40353 q = 1) (hb : d287735 q = 1) : d296261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40353, d296261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d40353, d296261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d287735 q = 1) (hb : d289322 q = 1) : d296262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289322, d296262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d289322, d296262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d287735 q = 1) (hb : d289323 q = 1) : d296263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289323, d296263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d289323, d296263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d287735 q = 1) (hb : d289324 q = 1) : d296264 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289324, d296264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d289324, d296264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d287735 q = 1) (hb : d289325 q = 1) : d296265 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289325, d296265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289325, d296265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro94159 (p : Pattern) (ha : d287735 p = 1) (hb : d289332 p = 1) : d296274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40347 q = 1) (hb : d287735 q = 1) : d296257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40347, d296257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94156 q ha hb
    | true =>
      simp only [d40347, d296257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94133 q ha hb
  have h2 (q : Pattern) (ha : d287735 q = 1) (hb : d289321 q = 1) : d296258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289321, d296258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289321, d296258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d40352 q = 1) (hb : d287735 q = 1) : d296260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40352, d296260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94157 q ha hb
    | true =>
      simp only [d40352, d296260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40353 q = 1) (hb : d287735 q = 1) : d296261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40353, d296261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40353, d296261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289322 q = 1) : d296262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289322, d296262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289322, d296262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289330 q = 1) : d296272 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289330, d296272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289330, d296272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287735 q = 1) (hb : d289331 q = 1) : d296273 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289331, d296273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289331, d296273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289332 q = 1) : d296274 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289332, d296274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289332, d296274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94160 (p : Pattern) (ha : d40382 p = 1) (hb : d287735 p = 1) : d296290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40372 q = 1) (hb : d287735 q = 1) : d296280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40372, d296280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40372, d296280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94147 q ha hb
  have h2 (q : Pattern) (ha : d40271 q = 1) (hb : d287735 q = 1) : d296209 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40271, d296209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94147 q ha hb
    | true =>
      simp only [d40271, d296209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40373 q = 1) (hb : d287735 q = 1) : d296281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40373, d296281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40373, d296281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40272 q = 1) (hb : d287735 q = 1) : d296210 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40272, d296210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40272, d296210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40374 q = 1) (hb : d287735 q = 1) : d296282 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40374, d296282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40374, d296282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40375 q = 1) (hb : d287735 q = 1) : d296283 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40375, d296283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40375, d296283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40201 q = 1) (hb : d287735 q = 1) : d296140 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40201, d296140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40201, d296140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94128 q ha hb
  have h8 (q : Pattern) (ha : d40158 q = 1) (hb : d287735 q = 1) : d296097 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40158, d296097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94128 q ha hb
    | true =>
      simp only [d40158, d296097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40202 q = 1) (hb : d287735 q = 1) : d296141 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40202, d296141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40202, d296141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40159 q = 1) (hb : d287735 q = 1) : d296098 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40159, d296098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40159, d296098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40203 q = 1) (hb : d287735 q = 1) : d296142 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40203, d296142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40203, d296142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40204 q = 1) (hb : d287735 q = 1) : d296143 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40204, d296143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40204, d296143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40376 q = 1) (hb : d287735 q = 1) : d296284 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40376, d296284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40376, d296284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40377 q = 1) (hb : d287735 q = 1) : d296285 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40377, d296285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40377, d296285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94148 q ha hb
  have h15 (q : Pattern) (ha : d40279 q = 1) (hb : d287735 q = 1) : d296217 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94148 q ha hb
    | true =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40378 q = 1) (hb : d287735 q = 1) : d296286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40378, d296286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40378, d296286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40280 q = 1) (hb : d287735 q = 1) : d296218 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40379 q = 1) (hb : d287735 q = 1) : d296287 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40379, d296287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40379, d296287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40380 q = 1) (hb : d287735 q = 1) : d296288 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40380, d296288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d40380, d296288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d287735 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d40381 q = 1) (hb : d287735 q = 1) : d296289 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40381, d296289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d40381, d296289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d40382 q = 1) (hb : d287735 q = 1) : d296290 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40382, d296290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40382, d296290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro94161 (p : Pattern) (ha : d40388 p = 1) (hb : d287735 p = 1) : d296296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40383 q = 1) (hb : d287735 q = 1) : d296291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40383, d296291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94160 q ha hb
    | true =>
      simp only [d40383, d296291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94136 q ha hb
  have h2 (q : Pattern) (ha : d40384 q = 1) (hb : d287735 q = 1) : d296292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40384, d296292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40384, d296292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40385 q = 1) (hb : d287735 q = 1) : d296293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40385, d296293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40385, d296293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d287735 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40207 q = 1) (hb : d287735 q = 1) : d296146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40207, d296146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94136 q ha hb
    | true =>
      simp only [d40207, d296146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40208 q = 1) (hb : d287735 q = 1) : d296147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40208, d296147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40208, d296147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40209 q = 1) (hb : d287735 q = 1) : d296148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40209, d296148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40209, d296148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40386 q = 1) (hb : d287735 q = 1) : d296294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40386, d296294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40386, d296294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d287735 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d40210 q = 1) (hb : d287735 q = 1) : d296149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40210, d296149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40210, d296149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40387 q = 1) (hb : d287735 q = 1) : d296295 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40387, d296295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40387, d296295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40388 q = 1) (hb : d287735 q = 1) : d296296 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40388, d296296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40388, d296296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro94162 (p : Pattern) (ha : d40394 p = 1) (hb : d287735 p = 1) : d296302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40389 q = 1) (hb : d287735 q = 1) : d296297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40389, d296297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94161 q ha hb
    | true =>
      simp only [d40389, d296297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40390 q = 1) (hb : d287735 q = 1) : d296298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40390, d296298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40390, d296298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40213 q = 1) (hb : d287735 q = 1) : d296152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40213, d296152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94137 q ha hb
    | true =>
      simp only [d40213, d296152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40214 q = 1) (hb : d287735 q = 1) : d296153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40214, d296153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40214, d296153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40391 q = 1) (hb : d287735 q = 1) : d296299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40391, d296299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40391, d296299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40392 q = 1) (hb : d287735 q = 1) : d296300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40392, d296300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40392, d296300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40393 q = 1) (hb : d287735 q = 1) : d296301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40393, d296301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40393, d296301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40394 q = 1) (hb : d287735 q = 1) : d296302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40394, d296302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40394, d296302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94163 (p : Pattern) (ha : d40419 p = 1) (hb : d287735 p = 1) : d296308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40213 q = 1) (hb : d287735 q = 1) : d296152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40213, d296152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94137 q ha hb
    | true =>
      simp only [d40213, d296152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40214 q = 1) (hb : d287735 q = 1) : d296153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40214, d296153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40214, d296153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40416 q = 1) (hb : d287735 q = 1) : d296305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40416, d296305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40416, d296305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40417 q = 1) (hb : d287735 q = 1) : d296306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40417, d296306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40417, d296306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40418 q = 1) (hb : d287735 q = 1) : d296307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40418, d296307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40418, d296307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40419 q = 1) (hb : d287735 q = 1) : d296308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40419, d296308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40419, d296308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94164 (p : Pattern) (ha : d287735 p = 1) (hb : d289342 p = 1) : d296314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40395 q = 1) (hb : d287735 q = 1) : d296303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40395, d296303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94162 q ha hb
    | true =>
      simp only [d40395, d296303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94138 q ha hb
  have h2 (q : Pattern) (ha : d287735 q = 1) (hb : d289338 q = 1) : d296304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289338, d296304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289338, d296304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d40420 q = 1) (hb : d287735 q = 1) : d296309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40420, d296309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94163 q ha hb
    | true =>
      simp only [d40420, d296309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40421 q = 1) (hb : d287735 q = 1) : d296310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40421, d296310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40421, d296310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289339 q = 1) : d296311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289339, d296311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289339, d296311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289340 q = 1) : d296312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289340, d296312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289340, d296312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287735 q = 1) (hb : d289341 q = 1) : d296313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289341, d296313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289341, d296313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289342 q = 1) : d296314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289342, d296314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289342, d296314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94165 (p : Pattern) (ha : d287735 p = 1) (hb : d289348 p = 1) : d296320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40241 q = 1) (hb : d287735 q = 1) : d296180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40241, d296180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40241, d296180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94141 q ha hb
  have h2 (q : Pattern) (ha : d40242 q = 1) (hb : d287735 q = 1) : d296181 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40242, d296181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40242, d296181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40248 q = 1) (hb : d287735 q = 1) : d296187 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40248, d296187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94141 q ha hb
    | true =>
      simp only [d40248, d296187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94142 q ha hb
  have h4 (q : Pattern) (ha : d40249 q = 1) (hb : d287735 q = 1) : d296188 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40249, d296188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40249, d296188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40250 q = 1) (hb : d287735 q = 1) : d296189 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d40250, d296189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40250, d296189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289326 q = 1) : d296266 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289326, d296266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94153 q ha hb
    | true =>
      simp only [d289326, d296266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94158 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d287735 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d40360 q = 1) (hb : d287735 q = 1) : d296268 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40360, d296268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94143 q ha hb
    | true =>
      simp only [d40360, d296268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287735 q = 1) (hb : d289327 q = 1) : d296269 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289327, d296269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289327, d296269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d287735 q = 1) (hb : d289328 q = 1) : d296270 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289328, d296270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289328, d296270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d287735 q = 1) (hb : d289329 q = 1) : d296271 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289329, d296271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d289329, d296271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d287735 q = 1) (hb : d289333 q = 1) : d296275 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289333, d296275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289333, d296275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94159 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d287735 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d287735 q = 1) (hb : d289334 q = 1) : d296276 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289334, d296276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289334, d296276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d287735 q = 1) (hb : d289335 q = 1) : d296277 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289335, d296277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289335, d296277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d287735 q = 1) (hb : d289336 q = 1) : d296278 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289336, d296278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289336, d296278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d287735 q = 1) (hb : d289337 q = 1) : d296279 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289337, d296279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289337, d296279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d287735 q = 1) (hb : d289343 q = 1) : d296315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289343, d296315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289343, d296315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94164 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d287735 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d287735 q = 1) (hb : d289344 q = 1) : d296316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289344, d296316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d289344, d296316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d287735 q = 1) (hb : d289345 q = 1) : d296317 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289345, d296317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d289345, d296317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d287735 q = 1) (hb : d289346 q = 1) : d296318 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289346, d296318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d289346, d296318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d287735 q = 1) (hb : d289347 q = 1) : d296319 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289347, d296319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d289347, d296319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d287735 q = 1) (hb : d289348 q = 1) : d296320 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289348, d296320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289348, d296320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro94166 (p : Pattern) (ha : d287735 p = 1) (hb : d289354 p = 1) : d296326 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d287735 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d287735 q = 1) (hb : d289311 q = 1) : d296170 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289311, d296170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289311, d296170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94140 q ha hb
  have h3 (q : Pattern) (ha : d287735 q = 1) (hb : d289312 q = 1) : d296171 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289312, d296171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289312, d296171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287735 q = 1) (hb : d289313 q = 1) : d296172 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289313, d296172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289313, d296172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289314 q = 1) : d296173 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289314, d296173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289314, d296173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289315 q = 1) : d296174 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289315, d296174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289315, d296174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287735 q = 1) (hb : d289349 q = 1) : d296321 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289349, d296321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289349, d296321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94165 q ha hb
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289350 q = 1) : d296322 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289350, d296322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289350, d296322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287735 q = 1) (hb : d289351 q = 1) : d296323 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289351, d296323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289351, d296323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287735 q = 1) (hb : d289352 q = 1) : d296324 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289352, d296324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289352, d296324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d287735 q = 1) (hb : d289353 q = 1) : d296325 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289353, d296325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289353, d296325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d287735 q = 1) (hb : d289354 q = 1) : d296326 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289354, d296326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289354, d296326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro94167 (p : Pattern) (ha : d40440 p = 1) (hb : d287735 p = 1) : d296329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40285 q = 1) (hb : d287735 q = 1) : d296223 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40285, d296223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94149 q ha hb
    | true =>
      simp only [d40285, d296223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94129 q ha hb
  have h2 (q : Pattern) (ha : d40286 q = 1) (hb : d287735 q = 1) : d296224 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40286, d296224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40286, d296224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40287 q = 1) (hb : d287735 q = 1) : d296225 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40287, d296225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40287, d296225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d287735 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40164 q = 1) (hb : d287735 q = 1) : d296103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40164, d296103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94129 q ha hb
    | true =>
      simp only [d40164, d296103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40165 q = 1) (hb : d287735 q = 1) : d296104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40165, d296104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40165, d296104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40166 q = 1) (hb : d287735 q = 1) : d296105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40166, d296105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40166, d296105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40288 q = 1) (hb : d287735 q = 1) : d296226 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40288, d296226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40288, d296226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40438 q = 1) (hb : d287735 q = 1) : d296327 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40438, d296327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40438, d296327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40439 q = 1) (hb : d287735 q = 1) : d296328 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40439, d296328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40439, d296328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40440 q = 1) (hb : d287735 q = 1) : d296329 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40440, d296329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40440, d296329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro94168 (p : Pattern) (ha : d40444 p = 1) (hb : d287735 p = 1) : d296333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d287735 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40164 q = 1) (hb : d287735 q = 1) : d296103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40164, d296103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94129 q ha hb
    | true =>
      simp only [d40164, d296103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40165 q = 1) (hb : d287735 q = 1) : d296104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40165, d296104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40165, d296104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40166 q = 1) (hb : d287735 q = 1) : d296105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40166, d296105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40166, d296105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40438 q = 1) (hb : d287735 q = 1) : d296327 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40438, d296327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40438, d296327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40443 q = 1) (hb : d287735 q = 1) : d296332 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40443, d296332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40443, d296332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40444 q = 1) (hb : d287735 q = 1) : d296333 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40444, d296333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40444, d296333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro94169 (p : Pattern) (ha : d40450 p = 1) (hb : d287735 p = 1) : d296339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d287735 q = 1) : d296330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94167 q ha hb
    | true =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d287735 q = 1) : d296331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40447 q = 1) (hb : d287735 q = 1) : d296336 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40448 q = 1) (hb : d287735 q = 1) : d296337 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40448, d296337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40448, d296337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40449 q = 1) (hb : d287735 q = 1) : d296338 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40449, d296338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40449, d296338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40450 q = 1) (hb : d287735 q = 1) : d296339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40450, d296339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40450, d296339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94170 (p : Pattern) (ha : d40454 p = 1) (hb : d287735 p = 1) : d296343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40451 q = 1) (hb : d287735 q = 1) : d296340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40452 q = 1) (hb : d287735 q = 1) : d296341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40452, d296341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40452, d296341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40453 q = 1) (hb : d287735 q = 1) : d296342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40453, d296342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40453, d296342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40454 q = 1) (hb : d287735 q = 1) : d296343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40454, d296343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40454, d296343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94171 (p : Pattern) (ha : d40460 p = 1) (hb : d287735 p = 1) : d296349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40455 q = 1) (hb : d287735 q = 1) : d296344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40455, d296344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94169 q ha hb
    | true =>
      simp only [d40455, d296344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94170 q ha hb
  have h2 (q : Pattern) (ha : d40456 q = 1) (hb : d287735 q = 1) : d296345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40456, d296345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40456, d296345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40457 q = 1) (hb : d287735 q = 1) : d296346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40457, d296346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40457, d296346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40458 q = 1) (hb : d287735 q = 1) : d296347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40458, d296347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40458, d296347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40459 q = 1) (hb : d287735 q = 1) : d296348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40459, d296348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40459, d296348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40460 q = 1) (hb : d287735 q = 1) : d296349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40460, d296349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40460, d296349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94172 (p : Pattern) (ha : d40463 p = 1) (hb : d287735 p = 1) : d296352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d287735 q = 1) : d296330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94167 q ha hb
    | true =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d287735 q = 1) : d296331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40447 q = 1) (hb : d287735 q = 1) : d296336 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40448 q = 1) (hb : d287735 q = 1) : d296337 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40448, d296337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40448, d296337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40449 q = 1) (hb : d287735 q = 1) : d296338 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40449, d296338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40449, d296338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40463 q = 1) (hb : d287735 q = 1) : d296352 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40463, d296352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40463, d296352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94173 (p : Pattern) (ha : d40464 p = 1) (hb : d287735 p = 1) : d296353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40451 q = 1) (hb : d287735 q = 1) : d296340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40452 q = 1) (hb : d287735 q = 1) : d296341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40452, d296341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40452, d296341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40453 q = 1) (hb : d287735 q = 1) : d296342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40453, d296342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40453, d296342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40464 q = 1) (hb : d287735 q = 1) : d296353 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40464, d296353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40464, d296353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94174 (p : Pattern) (ha : d40470 p = 1) (hb : d287735 p = 1) : d296359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40455 q = 1) (hb : d287735 q = 1) : d296344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40455, d296344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94169 q ha hb
    | true =>
      simp only [d40455, d296344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94170 q ha hb
  have h2 (q : Pattern) (ha : d40456 q = 1) (hb : d287735 q = 1) : d296345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40456, d296345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40456, d296345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40457 q = 1) (hb : d287735 q = 1) : d296346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40457, d296346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40457, d296346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40458 q = 1) (hb : d287735 q = 1) : d296347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40458, d296347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40458, d296347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40459 q = 1) (hb : d287735 q = 1) : d296348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40459, d296348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40459, d296348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40465 q = 1) (hb : d287735 q = 1) : d296354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40465, d296354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94172 q ha hb
    | true =>
      simp only [d40465, d296354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94173 q ha hb
  have h7 (q : Pattern) (ha : d40466 q = 1) (hb : d287735 q = 1) : d296355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40466, d296355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40466, d296355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40467 q = 1) (hb : d287735 q = 1) : d296356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40467, d296356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40467, d296356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40468 q = 1) (hb : d287735 q = 1) : d296357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40468, d296357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40468, d296357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40469 q = 1) (hb : d287735 q = 1) : d296358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40469, d296358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40469, d296358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40470 q = 1) (hb : d287735 q = 1) : d296359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40470, d296359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40470, d296359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94175 (p : Pattern) (ha : d40625 p = 1) (hb : d287735 p = 1) : d296465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40455 q = 1) (hb : d287735 q = 1) : d296344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40455, d296344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94169 q ha hb
    | true =>
      simp only [d40455, d296344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94170 q ha hb
  have h2 (q : Pattern) (ha : d40456 q = 1) (hb : d287735 q = 1) : d296345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40456, d296345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40456, d296345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40457 q = 1) (hb : d287735 q = 1) : d296346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40457, d296346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40457, d296346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40458 q = 1) (hb : d287735 q = 1) : d296347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40458, d296347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40458, d296347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40459 q = 1) (hb : d287735 q = 1) : d296348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40459, d296348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40459, d296348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40620 q = 1) (hb : d287735 q = 1) : d296460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40620, d296460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94170 q ha hb
    | true =>
      simp only [d40620, d296460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40621 q = 1) (hb : d287735 q = 1) : d296461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40621, d296461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40621, d296461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40622 q = 1) (hb : d287735 q = 1) : d296462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40622, d296462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40622, d296462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40623 q = 1) (hb : d287735 q = 1) : d296463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40623, d296463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40623, d296463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40624 q = 1) (hb : d287735 q = 1) : d296464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40624, d296464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40624, d296464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40625 q = 1) (hb : d287735 q = 1) : d296465 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40625, d296465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40625, d296465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94176 (p : Pattern) (ha : d40631 p = 1) (hb : d287735 p = 1) : d296471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40620 q = 1) (hb : d287735 q = 1) : d296460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40620, d296460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94170 q ha hb
    | true =>
      simp only [d40620, d296460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40621 q = 1) (hb : d287735 q = 1) : d296461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40621, d296461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40621, d296461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40622 q = 1) (hb : d287735 q = 1) : d296462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40622, d296462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40622, d296462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40623 q = 1) (hb : d287735 q = 1) : d296463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40623, d296463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40623, d296463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40624 q = 1) (hb : d287735 q = 1) : d296464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40624, d296464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40624, d296464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40626 q = 1) (hb : d287735 q = 1) : d296466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40626, d296466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94173 q ha hb
    | true =>
      simp only [d40626, d296466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40627 q = 1) (hb : d287735 q = 1) : d296467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40627, d296467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40627, d296467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40628 q = 1) (hb : d287735 q = 1) : d296468 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40628, d296468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40628, d296468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40629 q = 1) (hb : d287735 q = 1) : d296469 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40629, d296469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40629, d296469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40630 q = 1) (hb : d287735 q = 1) : d296470 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40630, d296470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40630, d296470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40631 q = 1) (hb : d287735 q = 1) : d296471 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40631, d296471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40631, d296471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94177 (p : Pattern) (ha : d40640 p = 1) (hb : d287735 p = 1) : d296480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40626 q = 1) (hb : d287735 q = 1) : d296466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40626, d296466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94173 q ha hb
    | true =>
      simp only [d40626, d296466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40627 q = 1) (hb : d287735 q = 1) : d296467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40627, d296467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40627, d296467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40628 q = 1) (hb : d287735 q = 1) : d296468 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40628, d296468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40628, d296468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40629 q = 1) (hb : d287735 q = 1) : d296469 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40629, d296469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40629, d296469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40630 q = 1) (hb : d287735 q = 1) : d296470 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40630, d296470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40630, d296470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40640 q = 1) (hb : d287735 q = 1) : d296480 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40640, d296480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40640, d296480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94178 (p : Pattern) (ha : d40683 p = 1) (hb : d287735 p = 1) : d296523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d287735 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40207 q = 1) (hb : d287735 q = 1) : d296146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40207, d296146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94136 q ha hb
    | true =>
      simp only [d40207, d296146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40208 q = 1) (hb : d287735 q = 1) : d296147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40208, d296147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40208, d296147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40209 q = 1) (hb : d287735 q = 1) : d296148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40209, d296148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40209, d296148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40673 q = 1) (hb : d287735 q = 1) : d296513 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40673, d296513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40673, d296513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40682 q = 1) (hb : d287735 q = 1) : d296522 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40682, d296522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40682, d296522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40683 q = 1) (hb : d287735 q = 1) : d296523 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40683, d296523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40683, d296523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro94179 (p : Pattern) (ha : d40739 p = 1) (hb : d287735 p = 1) : d296546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40684 q = 1) (hb : d287735 q = 1) : d296524 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40684, d296524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94178 q ha hb
    | true =>
      simp only [d40684, d296524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40685 q = 1) (hb : d287735 q = 1) : d296525 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40685, d296525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40685, d296525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40736 q = 1) (hb : d287735 q = 1) : d296543 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40736, d296543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40736, d296543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40737 q = 1) (hb : d287735 q = 1) : d296544 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40737, d296544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40737, d296544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40738 q = 1) (hb : d287735 q = 1) : d296545 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40738, d296545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40738, d296545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40739 q = 1) (hb : d287735 q = 1) : d296546 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40739, d296546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40739, d296546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94180 (p : Pattern) (ha : d40745 p = 1) (hb : d287735 p = 1) : d296552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40740 q = 1) (hb : d287735 q = 1) : d296547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40740, d296547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94179 q ha hb
    | true =>
      simp only [d40740, d296547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40741 q = 1) (hb : d287735 q = 1) : d296548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40741, d296548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40741, d296548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40742 q = 1) (hb : d287735 q = 1) : d296549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40742, d296549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40742, d296549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40743 q = 1) (hb : d287735 q = 1) : d296550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40743, d296550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40743, d296550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40744 q = 1) (hb : d287735 q = 1) : d296551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40744, d296551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40744, d296551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40745 q = 1) (hb : d287735 q = 1) : d296552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40745, d296552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40745, d296552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94181 (p : Pattern) (ha : d40475 p = 1) (hb : d287735 p = 1) : d296364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d287735 q = 1) : d296330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94167 q ha hb
    | true =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d287735 q = 1) : d296331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40447 q = 1) (hb : d287735 q = 1) : d296336 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40448 q = 1) (hb : d287735 q = 1) : d296337 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40448, d296337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40448, d296337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40474 q = 1) (hb : d287735 q = 1) : d296363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40474, d296363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40474, d296363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40475 q = 1) (hb : d287735 q = 1) : d296364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40475, d296364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40475, d296364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94182 (p : Pattern) (ha : d40477 p = 1) (hb : d287735 p = 1) : d296366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40451 q = 1) (hb : d287735 q = 1) : d296340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40452 q = 1) (hb : d287735 q = 1) : d296341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40452, d296341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40452, d296341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40476 q = 1) (hb : d287735 q = 1) : d296365 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40476, d296365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40476, d296365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40477 q = 1) (hb : d287735 q = 1) : d296366 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40477, d296366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40477, d296366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94183 (p : Pattern) (ha : d40484 p = 1) (hb : d287735 p = 1) : d296373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d287735 q = 1) : d296330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94167 q ha hb
    | true =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d287735 q = 1) : d296331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40447 q = 1) (hb : d287735 q = 1) : d296336 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40482 q = 1) (hb : d287735 q = 1) : d296371 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40482, d296371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40482, d296371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40483 q = 1) (hb : d287735 q = 1) : d296372 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40483, d296372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40483, d296372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40484 q = 1) (hb : d287735 q = 1) : d296373 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40484, d296373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40484, d296373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94184 (p : Pattern) (ha : d40487 p = 1) (hb : d287735 p = 1) : d296376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40451 q = 1) (hb : d287735 q = 1) : d296340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40485 q = 1) (hb : d287735 q = 1) : d296374 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40485, d296374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40485, d296374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40486 q = 1) (hb : d287735 q = 1) : d296375 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40486, d296375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40486, d296375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40487 q = 1) (hb : d287735 q = 1) : d296376 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40487, d296376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40487, d296376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94185 (p : Pattern) (ha : d40492 p = 1) (hb : d287735 p = 1) : d296380 p = 1 := by
  have h0 (q : Pattern) (ha : d40491 q = 1) (hb : d253269 q = 1) : d40491 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40263 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40492 q = 1) (hb : d287735 q = 1) : d296380 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d40492, d287735, d296380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40492, d287735, d296380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro94186 (p : Pattern) (ha : d40497 p = 1) (hb : d287735 p = 1) : d296384 p = 1 := by
  have h0 (q : Pattern) (ha : d40496 q = 1) (hb : d253269 q = 1) : d40496 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9579 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40497 q = 1) (hb : d287735 q = 1) : d296384 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d40497, d287735, d296384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40497, d287735, d296384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro94187 (p : Pattern) (ha : d40503 p = 1) (hb : d287735 p = 1) : d296390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40493 q = 1) (hb : d287735 q = 1) : d296381 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40493, d296381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94185 q ha hb
    | true =>
      simp only [d40493, d296381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40494 q = 1) (hb : d287735 q = 1) : d296382 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40494, d296382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40494, d296382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40265 q = 1) (hb : d287735 q = 1) : d296203 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94146 q ha hb
    | true =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40266 q = 1) (hb : d287735 q = 1) : d296204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40495 q = 1) (hb : d287735 q = 1) : d296383 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40495, d296383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40495, d296383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40498 q = 1) (hb : d287735 q = 1) : d296385 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40498, d296385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94186 q ha hb
    | true =>
      simp only [d40498, d296385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40499 q = 1) (hb : d287735 q = 1) : d296386 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40499, d296386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40499, d296386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40152 q = 1) (hb : d287735 q = 1) : d296091 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94127 q ha hb
    | true =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40153 q = 1) (hb : d287735 q = 1) : d296092 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40500 q = 1) (hb : d287735 q = 1) : d296387 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40500, d296387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40500, d296387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40501 q = 1) (hb : d287735 q = 1) : d296388 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40501, d296388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40501, d296388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40502 q = 1) (hb : d287735 q = 1) : d296389 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40502, d296389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40502, d296389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40267 q = 1) (hb : d287735 q = 1) : d296205 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d20 q = 1) (hb : d287735 q = 1) : d20 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d40154 q = 1) (hb : d287735 q = 1) : d296093 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40268 q = 1) (hb : d287735 q = 1) : d296206 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40268, d296206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40268, d296206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40269 q = 1) (hb : d287735 q = 1) : d296207 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40269, d296207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40269, d296207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40503 q = 1) (hb : d287735 q = 1) : d296390 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40503, d296390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40503, d296390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro94188 (p : Pattern) (ha : d40508 p = 1) (hb : d287735 p = 1) : d296395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40265 q = 1) (hb : d287735 q = 1) : d296203 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94146 q ha hb
    | true =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40266 q = 1) (hb : d287735 q = 1) : d296204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40152 q = 1) (hb : d287735 q = 1) : d296091 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94127 q ha hb
    | true =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40153 q = 1) (hb : d287735 q = 1) : d296092 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40267 q = 1) (hb : d287735 q = 1) : d296205 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d287735 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40154 q = 1) (hb : d287735 q = 1) : d296093 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40268 q = 1) (hb : d287735 q = 1) : d296206 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40268, d296206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40268, d296206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40269 q = 1) (hb : d287735 q = 1) : d296207 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40269, d296207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40269, d296207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40276 q = 1) (hb : d287735 q = 1) : d296214 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40276, d296214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40276, d296214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40277 q = 1) (hb : d287735 q = 1) : d296215 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40277, d296215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40277, d296215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40508 q = 1) (hb : d287735 q = 1) : d296395 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40508, d296395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40508, d296395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro94189 (p : Pattern) (ha : d40516 p = 1) (hb : d287735 p = 1) : d296403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40265 q = 1) (hb : d287735 q = 1) : d296203 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94146 q ha hb
    | true =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40266 q = 1) (hb : d287735 q = 1) : d296204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40152 q = 1) (hb : d287735 q = 1) : d296091 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94127 q ha hb
    | true =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40153 q = 1) (hb : d287735 q = 1) : d296092 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40267 q = 1) (hb : d287735 q = 1) : d296205 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40514 q = 1) (hb : d287735 q = 1) : d296401 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40514, d296401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40514, d296401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40515 q = 1) (hb : d287735 q = 1) : d296402 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40515, d296402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40515, d296402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d287735 q = 1) : d20 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d40154 q = 1) (hb : d287735 q = 1) : d296093 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40276 q = 1) (hb : d287735 q = 1) : d296214 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40276, d296214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40276, d296214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40277 q = 1) (hb : d287735 q = 1) : d296215 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40277, d296215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40277, d296215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40516 q = 1) (hb : d287735 q = 1) : d296403 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40516, d296403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40516, d296403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro94190 (p : Pattern) (ha : d40522 p = 1) (hb : d287735 p = 1) : d296409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40504 q = 1) (hb : d287735 q = 1) : d296391 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40504, d296391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94187 q ha hb
    | true =>
      simp only [d40504, d296391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40505 q = 1) (hb : d287735 q = 1) : d296392 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40505, d296392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40505, d296392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40506 q = 1) (hb : d287735 q = 1) : d296393 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40506, d296393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40506, d296393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40507 q = 1) (hb : d287735 q = 1) : d296394 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40507, d296394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40507, d296394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40509 q = 1) (hb : d287735 q = 1) : d296396 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40509, d296396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94188 q ha hb
    | true =>
      simp only [d40509, d296396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40510 q = 1) (hb : d287735 q = 1) : d296397 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40510, d296397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40510, d296397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40511 q = 1) (hb : d287735 q = 1) : d296398 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40511, d296398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40511, d296398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40512 q = 1) (hb : d287735 q = 1) : d296399 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40512, d296399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40512, d296399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40513 q = 1) (hb : d287735 q = 1) : d296400 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40513, d296400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40513, d296400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40517 q = 1) (hb : d287735 q = 1) : d296404 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40517, d296404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94189 q ha hb
    | true =>
      simp only [d40517, d296404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40518 q = 1) (hb : d287735 q = 1) : d296405 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40518, d296405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40518, d296405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40519 q = 1) (hb : d287735 q = 1) : d296406 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40519, d296406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40519, d296406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40520 q = 1) (hb : d287735 q = 1) : d296407 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40520, d296407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40520, d296407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d40279 q = 1) (hb : d287735 q = 1) : d296217 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94148 q ha hb
    | true =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d40280 q = 1) (hb : d287735 q = 1) : d296218 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40281 q = 1) (hb : d287735 q = 1) : d296219 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40281, d296219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40281, d296219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40282 q = 1) (hb : d287735 q = 1) : d296220 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40282, d296220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40282, d296220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40521 q = 1) (hb : d287735 q = 1) : d296408 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40521, d296408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40521, d296408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40522 q = 1) (hb : d287735 q = 1) : d296409 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40522, d296409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40522, d296409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro94191 (p : Pattern) (ha : d40526 p = 1) (hb : d287735 p = 1) : d296413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40279 q = 1) (hb : d287735 q = 1) : d296217 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94148 q ha hb
    | true =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40280 q = 1) (hb : d287735 q = 1) : d296218 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40281 q = 1) (hb : d287735 q = 1) : d296219 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40281, d296219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40281, d296219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40282 q = 1) (hb : d287735 q = 1) : d296220 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40282, d296220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40282, d296220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d287735 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40283 q = 1) (hb : d287735 q = 1) : d296221 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40283, d296221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40283, d296221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d287735 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d40526 q = 1) (hb : d287735 q = 1) : d296413 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40526, d296413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40526, d296413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94192 (p : Pattern) (ha : d40532 p = 1) (hb : d287735 p = 1) : d296419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40523 q = 1) (hb : d287735 q = 1) : d296410 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40523, d296410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94190 q ha hb
    | true =>
      simp only [d40523, d296410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94149 q ha hb
  have h2 (q : Pattern) (ha : d40524 q = 1) (hb : d287735 q = 1) : d296411 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40524, d296411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40524, d296411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40525 q = 1) (hb : d287735 q = 1) : d296412 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40525, d296412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40525, d296412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40527 q = 1) (hb : d287735 q = 1) : d296414 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40527, d296414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94149 q ha hb
    | true =>
      simp only [d40527, d296414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94191 q ha hb
  have h5 (q : Pattern) (ha : d40528 q = 1) (hb : d287735 q = 1) : d296415 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40528, d296415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40528, d296415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40529 q = 1) (hb : d287735 q = 1) : d296416 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40529, d296416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40529, d296416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40530 q = 1) (hb : d287735 q = 1) : d296417 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40530, d296417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40530, d296417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40285 q = 1) (hb : d287735 q = 1) : d296223 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40285, d296223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94149 q ha hb
    | true =>
      simp only [d40285, d296223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94129 q ha hb
  have h9 (q : Pattern) (ha : d40286 q = 1) (hb : d287735 q = 1) : d296224 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40286, d296224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40286, d296224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40287 q = 1) (hb : d287735 q = 1) : d296225 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40287, d296225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40287, d296225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d287735 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d40164 q = 1) (hb : d287735 q = 1) : d296103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40164, d296103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94129 q ha hb
    | true =>
      simp only [d40164, d296103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40165 q = 1) (hb : d287735 q = 1) : d296104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40165, d296104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40165, d296104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40166 q = 1) (hb : d287735 q = 1) : d296105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40166, d296105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40166, d296105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d40288 q = 1) (hb : d287735 q = 1) : d296226 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40288, d296226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40288, d296226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40531 q = 1) (hb : d287735 q = 1) : d296418 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40531, d296418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40531, d296418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40532 q = 1) (hb : d287735 q = 1) : d296419 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40532, d296419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40532, d296419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro94193 (p : Pattern) (ha : d40538 p = 1) (hb : d287735 p = 1) : d296425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40533 q = 1) (hb : d287735 q = 1) : d296420 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40533, d296420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94192 q ha hb
    | true =>
      simp only [d40533, d296420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40534 q = 1) (hb : d287735 q = 1) : d296421 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40534, d296421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40534, d296421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40441 q = 1) (hb : d287735 q = 1) : d296330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94167 q ha hb
    | true =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40442 q = 1) (hb : d287735 q = 1) : d296331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40535 q = 1) (hb : d287735 q = 1) : d296422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40535, d296422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40535, d296422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40536 q = 1) (hb : d287735 q = 1) : d296423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40536, d296423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40536, d296423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40537 q = 1) (hb : d287735 q = 1) : d296424 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40537, d296424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40537, d296424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40538 q = 1) (hb : d287735 q = 1) : d296425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40538, d296425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40538, d296425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94194 (p : Pattern) (ha : d40588 p = 1) (hb : d287735 p = 1) : d296431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d287735 q = 1) : d296330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94167 q ha hb
    | true =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d287735 q = 1) : d296331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40585 q = 1) (hb : d287735 q = 1) : d296428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40585, d296428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40585, d296428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40586 q = 1) (hb : d287735 q = 1) : d296429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40586, d296429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40586, d296429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40587 q = 1) (hb : d287735 q = 1) : d296430 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40587, d296430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40587, d296430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40588 q = 1) (hb : d287735 q = 1) : d296431 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40588, d296431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40588, d296431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94195 (p : Pattern) (ha : d287735 p = 1) (hb : d289359 p = 1) : d296437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40478 q = 1) (hb : d287735 q = 1) : d296367 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40478, d296367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94181 q ha hb
    | true =>
      simp only [d40478, d296367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94182 q ha hb
  have h2 (q : Pattern) (ha : d40479 q = 1) (hb : d287735 q = 1) : d296368 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40479, d296368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40479, d296368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40480 q = 1) (hb : d287735 q = 1) : d296369 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40480, d296369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40480, d296369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40481 q = 1) (hb : d287735 q = 1) : d296370 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40481, d296370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40481, d296370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40488 q = 1) (hb : d287735 q = 1) : d296377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40488, d296377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94183 q ha hb
    | true =>
      simp only [d40488, d296377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94184 q ha hb
  have h6 (q : Pattern) (ha : d40489 q = 1) (hb : d287735 q = 1) : d296378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40489, d296378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40489, d296378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40490 q = 1) (hb : d287735 q = 1) : d296379 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40490, d296379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40490, d296379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40539 q = 1) (hb : d287735 q = 1) : d296426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40539, d296426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94193 q ha hb
    | true =>
      simp only [d40539, d296426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94169 q ha hb
  have h9 (q : Pattern) (ha : d287735 q = 1) (hb : d289355 q = 1) : d296427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289355, d296427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d289355, d296427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d40589 q = 1) (hb : d287735 q = 1) : d296432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40589, d296432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94194 q ha hb
    | true =>
      simp only [d40589, d296432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40590 q = 1) (hb : d287735 q = 1) : d296433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40590, d296433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40590, d296433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d287735 q = 1) (hb : d289356 q = 1) : d296434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289356, d296434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289356, d296434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d287735 q = 1) (hb : d289357 q = 1) : d296435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289357, d296435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d289357, d296435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d287735 q = 1) (hb : d289358 q = 1) : d296436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289358, d296436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289358, d296436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d287735 q = 1) (hb : d289359 q = 1) : d296437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289359, d296437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289359, d296437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94196 (p : Pattern) (ha : d40595 p = 1) (hb : d287735 p = 1) : d296438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d287735 q = 1) : d296330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94167 q ha hb
    | true =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d287735 q = 1) : d296331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40447 q = 1) (hb : d287735 q = 1) : d296336 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40448 q = 1) (hb : d287735 q = 1) : d296337 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40448, d296337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40448, d296337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40474 q = 1) (hb : d287735 q = 1) : d296363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40474, d296363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40474, d296363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40595 q = 1) (hb : d287735 q = 1) : d296438 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40595, d296438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40595, d296438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94197 (p : Pattern) (ha : d40596 p = 1) (hb : d287735 p = 1) : d296439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40451 q = 1) (hb : d287735 q = 1) : d296340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40452 q = 1) (hb : d287735 q = 1) : d296341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40452, d296341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40452, d296341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40476 q = 1) (hb : d287735 q = 1) : d296365 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40476, d296365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40476, d296365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40596 q = 1) (hb : d287735 q = 1) : d296439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40596, d296439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40596, d296439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94198 (p : Pattern) (ha : d40601 p = 1) (hb : d287735 p = 1) : d296444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d287735 q = 1) : d296330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94167 q ha hb
    | true =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d287735 q = 1) : d296331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40447 q = 1) (hb : d287735 q = 1) : d296336 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40447, d296336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40482 q = 1) (hb : d287735 q = 1) : d296371 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40482, d296371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40482, d296371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40483 q = 1) (hb : d287735 q = 1) : d296372 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40483, d296372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40483, d296372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40601 q = 1) (hb : d287735 q = 1) : d296444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40601, d296444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40601, d296444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94199 (p : Pattern) (ha : d40602 p = 1) (hb : d287735 p = 1) : d296445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40445 q = 1) (hb : d287735 q = 1) : d296334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94168 q ha hb
    | true =>
      simp only [d40445, d296334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40446 q = 1) (hb : d287735 q = 1) : d296335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d296335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40451 q = 1) (hb : d287735 q = 1) : d296340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40451, d296340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40485 q = 1) (hb : d287735 q = 1) : d296374 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40485, d296374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40485, d296374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40486 q = 1) (hb : d287735 q = 1) : d296375 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40486, d296375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40486, d296375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40602 q = 1) (hb : d287735 q = 1) : d296445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40602, d296445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40602, d296445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94200 (p : Pattern) (ha : d40606 p = 1) (hb : d287735 p = 1) : d296449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40533 q = 1) (hb : d287735 q = 1) : d296420 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40533, d296420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94192 q ha hb
    | true =>
      simp only [d40533, d296420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40534 q = 1) (hb : d287735 q = 1) : d296421 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40534, d296421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40534, d296421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40441 q = 1) (hb : d287735 q = 1) : d296330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94167 q ha hb
    | true =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40442 q = 1) (hb : d287735 q = 1) : d296331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40535 q = 1) (hb : d287735 q = 1) : d296422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40535, d296422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40535, d296422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40536 q = 1) (hb : d287735 q = 1) : d296423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40536, d296423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40536, d296423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40537 q = 1) (hb : d287735 q = 1) : d296424 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40537, d296424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40537, d296424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40606 q = 1) (hb : d287735 q = 1) : d296449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40606, d296449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40606, d296449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94201 (p : Pattern) (ha : d40612 p = 1) (hb : d287735 p = 1) : d296452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d287735 q = 1) : d296330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94167 q ha hb
    | true =>
      simp only [d40441, d296330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d287735 q = 1) : d296331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d296331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40585 q = 1) (hb : d287735 q = 1) : d296428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40585, d296428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40585, d296428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40586 q = 1) (hb : d287735 q = 1) : d296429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40586, d296429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40586, d296429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40587 q = 1) (hb : d287735 q = 1) : d296430 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40587, d296430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40587, d296430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40612 q = 1) (hb : d287735 q = 1) : d296452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40612, d296452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40612, d296452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94202 (p : Pattern) (ha : d287735 p = 1) (hb : d289364 p = 1) : d296458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40478 q = 1) (hb : d287735 q = 1) : d296367 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40478, d296367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94181 q ha hb
    | true =>
      simp only [d40478, d296367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94182 q ha hb
  have h2 (q : Pattern) (ha : d40479 q = 1) (hb : d287735 q = 1) : d296368 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40479, d296368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40479, d296368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40480 q = 1) (hb : d287735 q = 1) : d296369 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40480, d296369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40480, d296369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40481 q = 1) (hb : d287735 q = 1) : d296370 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40481, d296370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40481, d296370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40488 q = 1) (hb : d287735 q = 1) : d296377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40488, d296377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94183 q ha hb
    | true =>
      simp only [d40488, d296377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94184 q ha hb
  have h6 (q : Pattern) (ha : d40489 q = 1) (hb : d287735 q = 1) : d296378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40489, d296378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40489, d296378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40490 q = 1) (hb : d287735 q = 1) : d296379 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40490, d296379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40490, d296379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40539 q = 1) (hb : d287735 q = 1) : d296426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40539, d296426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94193 q ha hb
    | true =>
      simp only [d40539, d296426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94169 q ha hb
  have h9 (q : Pattern) (ha : d287735 q = 1) (hb : d289355 q = 1) : d296427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289355, d296427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d289355, d296427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d40589 q = 1) (hb : d287735 q = 1) : d296432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40589, d296432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94194 q ha hb
    | true =>
      simp only [d40589, d296432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40590 q = 1) (hb : d287735 q = 1) : d296433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40590, d296433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40590, d296433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d287735 q = 1) (hb : d289356 q = 1) : d296434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289356, d296434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289356, d296434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d287735 q = 1) (hb : d289357 q = 1) : d296435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289357, d296435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d289357, d296435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d287735 q = 1) (hb : d289358 q = 1) : d296436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289358, d296436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289358, d296436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d40597 q = 1) (hb : d287735 q = 1) : d296440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40597, d296440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94196 q ha hb
    | true =>
      simp only [d40597, d296440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94197 q ha hb
  have h16 (q : Pattern) (ha : d40598 q = 1) (hb : d287735 q = 1) : d296441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40598, d296441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40598, d296441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40599 q = 1) (hb : d287735 q = 1) : d296442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40599, d296442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40599, d296442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40600 q = 1) (hb : d287735 q = 1) : d296443 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40600, d296443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40600, d296443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40603 q = 1) (hb : d287735 q = 1) : d296446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40603, d296446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94198 q ha hb
    | true =>
      simp only [d40603, d296446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94199 q ha hb
  have h20 (q : Pattern) (ha : d40604 q = 1) (hb : d287735 q = 1) : d296447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40604, d296447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40604, d296447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d40605 q = 1) (hb : d287735 q = 1) : d296448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40605, d296448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d40605, d296448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d40607 q = 1) (hb : d287735 q = 1) : d296450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40607, d296450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94200 q ha hb
    | true =>
      simp only [d40607, d296450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94172 q ha hb
  have h23 (q : Pattern) (ha : d287735 q = 1) (hb : d289360 q = 1) : d296451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289360, d296451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d289360, d296451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d40613 q = 1) (hb : d287735 q = 1) : d296453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40613, d296453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94201 q ha hb
    | true =>
      simp only [d40613, d296453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d40614 q = 1) (hb : d287735 q = 1) : d296454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40614, d296454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d40614, d296454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d287735 q = 1) (hb : d289361 q = 1) : d296455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289361, d296455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d289361, d296455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d287735 q = 1) (hb : d289362 q = 1) : d296456 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289362, d296456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d289362, d296456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d287735 q = 1) (hb : d289363 q = 1) : d296457 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289363, d296457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d289363, d296457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d287735 q = 1) (hb : d289364 q = 1) : d296458 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289364, d296458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289364, d296458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro94203 (p : Pattern) (ha : d287735 p = 1) (hb : d289371 p = 1) : d296478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40607 q = 1) (hb : d287735 q = 1) : d296450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40607, d296450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94200 q ha hb
    | true =>
      simp only [d40607, d296450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94172 q ha hb
  have h2 (q : Pattern) (ha : d287735 q = 1) (hb : d289360 q = 1) : d296451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289360, d296451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289360, d296451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d40613 q = 1) (hb : d287735 q = 1) : d296453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40613, d296453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94201 q ha hb
    | true =>
      simp only [d40613, d296453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40614 q = 1) (hb : d287735 q = 1) : d296454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40614, d296454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40614, d296454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289361 q = 1) : d296455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289361, d296455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289361, d296455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289369 q = 1) : d296476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289369, d296476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289369, d296476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287735 q = 1) (hb : d289370 q = 1) : d296477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289370, d296477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289370, d296477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289371 q = 1) : d296478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289371, d296478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289371, d296478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94204 (p : Pattern) (ha : d40660 p = 1) (hb : d287735 p = 1) : d296500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40646 q = 1) (hb : d287735 q = 1) : d296486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40646, d296486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40646, d296486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94187 q ha hb
  have h2 (q : Pattern) (ha : d40504 q = 1) (hb : d287735 q = 1) : d296391 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40504, d296391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94187 q ha hb
    | true =>
      simp only [d40504, d296391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40647 q = 1) (hb : d287735 q = 1) : d296487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40647, d296487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40647, d296487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40505 q = 1) (hb : d287735 q = 1) : d296392 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40505, d296392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40505, d296392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40648 q = 1) (hb : d287735 q = 1) : d296488 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40648, d296488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40648, d296488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40649 q = 1) (hb : d287735 q = 1) : d296489 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40649, d296489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40649, d296489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40650 q = 1) (hb : d287735 q = 1) : d296490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40650, d296490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40650, d296490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94188 q ha hb
  have h8 (q : Pattern) (ha : d40509 q = 1) (hb : d287735 q = 1) : d296396 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40509, d296396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94188 q ha hb
    | true =>
      simp only [d40509, d296396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40651 q = 1) (hb : d287735 q = 1) : d296491 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40651, d296491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40651, d296491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40510 q = 1) (hb : d287735 q = 1) : d296397 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40510, d296397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40510, d296397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40652 q = 1) (hb : d287735 q = 1) : d296492 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40652, d296492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40652, d296492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40653 q = 1) (hb : d287735 q = 1) : d296493 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40653, d296493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40653, d296493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40654 q = 1) (hb : d287735 q = 1) : d296494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40654, d296494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40654, d296494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40655 q = 1) (hb : d287735 q = 1) : d296495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40655, d296495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40655, d296495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94189 q ha hb
  have h15 (q : Pattern) (ha : d40517 q = 1) (hb : d287735 q = 1) : d296404 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40517, d296404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94189 q ha hb
    | true =>
      simp only [d40517, d296404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40656 q = 1) (hb : d287735 q = 1) : d296496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40656, d296496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40656, d296496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40518 q = 1) (hb : d287735 q = 1) : d296405 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40518, d296405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d40518, d296405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40657 q = 1) (hb : d287735 q = 1) : d296497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40657, d296497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40657, d296497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40658 q = 1) (hb : d287735 q = 1) : d296498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40658, d296498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d40658, d296498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d40377 q = 1) (hb : d287735 q = 1) : d296285 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40377, d296285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40377, d296285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94148 q ha hb
  have h21 (q : Pattern) (ha : d40279 q = 1) (hb : d287735 q = 1) : d296217 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94148 q ha hb
    | true =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d40378 q = 1) (hb : d287735 q = 1) : d296286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40378, d296286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d40378, d296286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d40280 q = 1) (hb : d287735 q = 1) : d296218 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d40379 q = 1) (hb : d287735 q = 1) : d296287 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40379, d296287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d40379, d296287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d40380 q = 1) (hb : d287735 q = 1) : d296288 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40380, d296288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d40380, d296288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d40659 q = 1) (hb : d287735 q = 1) : d296499 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40659, d296499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d40659, d296499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d40660 q = 1) (hb : d287735 q = 1) : d296500 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40660, d296500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40660, d296500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro94205 (p : Pattern) (ha : d40664 p = 1) (hb : d287735 p = 1) : d296504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40377 q = 1) (hb : d287735 q = 1) : d296285 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40377, d296285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40377, d296285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94148 q ha hb
  have h2 (q : Pattern) (ha : d40279 q = 1) (hb : d287735 q = 1) : d296217 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94148 q ha hb
    | true =>
      simp only [d40279, d296217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40378 q = 1) (hb : d287735 q = 1) : d296286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40378, d296286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40378, d296286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40280 q = 1) (hb : d287735 q = 1) : d296218 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40280, d296218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40379 q = 1) (hb : d287735 q = 1) : d296287 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40379, d296287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40379, d296287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40380 q = 1) (hb : d287735 q = 1) : d296288 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40380, d296288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40380, d296288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d287735 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d40381 q = 1) (hb : d287735 q = 1) : d296289 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40381, d296289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40381, d296289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d287735 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d40664 q = 1) (hb : d287735 q = 1) : d296504 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40664, d296504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40664, d296504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro94206 (p : Pattern) (ha : d40670 p = 1) (hb : d287735 p = 1) : d296510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40661 q = 1) (hb : d287735 q = 1) : d296501 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40661, d296501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94204 q ha hb
    | true =>
      simp only [d40661, d296501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94160 q ha hb
  have h2 (q : Pattern) (ha : d40662 q = 1) (hb : d287735 q = 1) : d296502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40662, d296502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40662, d296502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40663 q = 1) (hb : d287735 q = 1) : d296503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40663, d296503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40663, d296503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40665 q = 1) (hb : d287735 q = 1) : d296505 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40665, d296505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94160 q ha hb
    | true =>
      simp only [d40665, d296505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94205 q ha hb
  have h5 (q : Pattern) (ha : d40666 q = 1) (hb : d287735 q = 1) : d296506 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40666, d296506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40666, d296506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40667 q = 1) (hb : d287735 q = 1) : d296507 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40667, d296507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40667, d296507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40668 q = 1) (hb : d287735 q = 1) : d296508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40668, d296508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40668, d296508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40383 q = 1) (hb : d287735 q = 1) : d296291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40383, d296291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94160 q ha hb
    | true =>
      simp only [d40383, d296291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94136 q ha hb
  have h9 (q : Pattern) (ha : d40384 q = 1) (hb : d287735 q = 1) : d296292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40384, d296292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40384, d296292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40385 q = 1) (hb : d287735 q = 1) : d296293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40385, d296293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40385, d296293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d287735 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d40207 q = 1) (hb : d287735 q = 1) : d296146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40207, d296146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94136 q ha hb
    | true =>
      simp only [d40207, d296146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40208 q = 1) (hb : d287735 q = 1) : d296147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40208, d296147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40208, d296147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40209 q = 1) (hb : d287735 q = 1) : d296148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40209, d296148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40209, d296148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d40386 q = 1) (hb : d287735 q = 1) : d296294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40386, d296294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40386, d296294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40669 q = 1) (hb : d287735 q = 1) : d296509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40669, d296509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40669, d296509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40670 q = 1) (hb : d287735 q = 1) : d296510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40670, d296510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40670, d296510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro94207 (p : Pattern) (ha : d40675 p = 1) (hb : d287735 p = 1) : d296515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40383 q = 1) (hb : d287735 q = 1) : d296291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40383, d296291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94160 q ha hb
    | true =>
      simp only [d40383, d296291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94136 q ha hb
  have h2 (q : Pattern) (ha : d40384 q = 1) (hb : d287735 q = 1) : d296292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40384, d296292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40384, d296292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40385 q = 1) (hb : d287735 q = 1) : d296293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40385, d296293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40385, d296293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d287735 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40207 q = 1) (hb : d287735 q = 1) : d296146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40207, d296146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94136 q ha hb
    | true =>
      simp only [d40207, d296146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40208 q = 1) (hb : d287735 q = 1) : d296147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40208, d296147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40208, d296147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40209 q = 1) (hb : d287735 q = 1) : d296148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40209, d296148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40209, d296148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40386 q = 1) (hb : d287735 q = 1) : d296294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40386, d296294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40386, d296294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40673 q = 1) (hb : d287735 q = 1) : d296513 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40673, d296513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40673, d296513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40674 q = 1) (hb : d287735 q = 1) : d296514 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40674, d296514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40674, d296514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40675 q = 1) (hb : d287735 q = 1) : d296515 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40675, d296515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40675, d296515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro94208 (p : Pattern) (ha : d40681 p = 1) (hb : d287735 p = 1) : d296521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40671 q = 1) (hb : d287735 q = 1) : d296511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40671, d296511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94206 q ha hb
    | true =>
      simp only [d40671, d296511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40672 q = 1) (hb : d287735 q = 1) : d296512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40672, d296512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40672, d296512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40676 q = 1) (hb : d287735 q = 1) : d296516 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40676, d296516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94207 q ha hb
    | true =>
      simp only [d40676, d296516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40677 q = 1) (hb : d287735 q = 1) : d296517 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40677, d296517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40677, d296517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40678 q = 1) (hb : d287735 q = 1) : d296518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40678, d296518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40678, d296518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40679 q = 1) (hb : d287735 q = 1) : d296519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40679, d296519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40679, d296519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40680 q = 1) (hb : d287735 q = 1) : d296520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40680, d296520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40680, d296520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40681 q = 1) (hb : d287735 q = 1) : d296521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40681, d296521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40681, d296521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94209 (p : Pattern) (ha : d40689 p = 1) (hb : d287735 p = 1) : d296529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40676 q = 1) (hb : d287735 q = 1) : d296516 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40676, d296516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94207 q ha hb
    | true =>
      simp only [d40676, d296516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40677 q = 1) (hb : d287735 q = 1) : d296517 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40677, d296517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40677, d296517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40684 q = 1) (hb : d287735 q = 1) : d296524 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40684, d296524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94178 q ha hb
    | true =>
      simp only [d40684, d296524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40685 q = 1) (hb : d287735 q = 1) : d296525 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40685, d296525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40685, d296525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40686 q = 1) (hb : d287735 q = 1) : d296526 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40686, d296526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40686, d296526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40687 q = 1) (hb : d287735 q = 1) : d296527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40687, d296527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40687, d296527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40688 q = 1) (hb : d287735 q = 1) : d296528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40688, d296528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40688, d296528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40689 q = 1) (hb : d287735 q = 1) : d296529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40689, d296529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40689, d296529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94210 (p : Pattern) (ha : d40728 p = 1) (hb : d287735 p = 1) : d296535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40676 q = 1) (hb : d287735 q = 1) : d296516 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40676, d296516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94207 q ha hb
    | true =>
      simp only [d40676, d296516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40677 q = 1) (hb : d287735 q = 1) : d296517 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40677, d296517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40677, d296517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40725 q = 1) (hb : d287735 q = 1) : d296532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40725, d296532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40725, d296532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40726 q = 1) (hb : d287735 q = 1) : d296533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40726, d296533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40726, d296533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40727 q = 1) (hb : d287735 q = 1) : d296534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40727, d296534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40727, d296534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40728 q = 1) (hb : d287735 q = 1) : d296535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40728, d296535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40728, d296535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94211 (p : Pattern) (ha : d287735 p = 1) (hb : d289381 p = 1) : d296541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40690 q = 1) (hb : d287735 q = 1) : d296530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40690, d296530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94208 q ha hb
    | true =>
      simp only [d40690, d296530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94209 q ha hb
  have h2 (q : Pattern) (ha : d287735 q = 1) (hb : d289377 q = 1) : d296531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289377, d296531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289377, d296531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d40729 q = 1) (hb : d287735 q = 1) : d296536 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40729, d296536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94210 q ha hb
    | true =>
      simp only [d40729, d296536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40730 q = 1) (hb : d287735 q = 1) : d296537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40730, d296537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40730, d296537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289378 q = 1) : d296538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289378, d296538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289378, d296538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289379 q = 1) : d296539 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289379, d296539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289379, d296539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287735 q = 1) (hb : d289380 q = 1) : d296540 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289380, d296540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289380, d296540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289381 q = 1) : d296541 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289381, d296541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289381, d296541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94212 (p : Pattern) (ha : d287735 p = 1) (hb : d289387 p = 1) : d296558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40461 q = 1) (hb : d287735 q = 1) : d296350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40461, d296350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40461, d296350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94171 q ha hb
  have h2 (q : Pattern) (ha : d40462 q = 1) (hb : d287735 q = 1) : d296351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40462, d296351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40462, d296351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40471 q = 1) (hb : d287735 q = 1) : d296360 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40471, d296360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94171 q ha hb
    | true =>
      simp only [d40471, d296360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94174 q ha hb
  have h4 (q : Pattern) (ha : d40472 q = 1) (hb : d287735 q = 1) : d296361 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40472, d296361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40472, d296361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40473 q = 1) (hb : d287735 q = 1) : d296362 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d40473, d296362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40473, d296362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289365 q = 1) : d296459 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289365, d296459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94195 q ha hb
    | true =>
      simp only [d289365, d296459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94202 q ha hb
  have h7 (q : Pattern) (ha : d40632 q = 1) (hb : d287735 q = 1) : d296472 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40632, d296472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94175 q ha hb
    | true =>
      simp only [d40632, d296472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94176 q ha hb
  have h8 (q : Pattern) (ha : d287735 q = 1) (hb : d289366 q = 1) : d296473 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289366, d296473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289366, d296473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d287735 q = 1) (hb : d289367 q = 1) : d296474 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289367, d296474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289367, d296474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d287735 q = 1) (hb : d289368 q = 1) : d296475 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289368, d296475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d289368, d296475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d287735 q = 1) (hb : d289372 q = 1) : d296479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289372, d296479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289372, d296479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94203 q ha hb
  have h12 (q : Pattern) (ha : d40641 q = 1) (hb : d287735 q = 1) : d296481 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40641, d296481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40641, d296481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94177 q ha hb
  have h13 (q : Pattern) (ha : d287735 q = 1) (hb : d289373 q = 1) : d296482 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289373, d296482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289373, d296482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d287735 q = 1) (hb : d289374 q = 1) : d296483 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289374, d296483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289374, d296483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d287735 q = 1) (hb : d289375 q = 1) : d296484 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289375, d296484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289375, d296484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d287735 q = 1) (hb : d289376 q = 1) : d296485 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289376, d296485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289376, d296485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d287735 q = 1) (hb : d289382 q = 1) : d296542 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289382, d296542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289382, d296542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94211 q ha hb
  have h18 (q : Pattern) (ha : d40746 q = 1) (hb : d287735 q = 1) : d296553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40746, d296553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40746, d296553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94180 q ha hb
  have h19 (q : Pattern) (ha : d287735 q = 1) (hb : d289383 q = 1) : d296554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289383, d296554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289383, d296554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d287735 q = 1) (hb : d289384 q = 1) : d296555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289384, d296555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d289384, d296555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d287735 q = 1) (hb : d289385 q = 1) : d296556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289385, d296556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d289385, d296556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d287735 q = 1) (hb : d289386 q = 1) : d296557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289386, d296557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d289386, d296557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d287735 q = 1) (hb : d289387 q = 1) : d296558 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289387, d296558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289387, d296558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro94213 (p : Pattern) (ha : d287735 p = 1) (hb : d289393 p = 1) : d296564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287735 q = 1) (hb : d289388 q = 1) : d296559 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289388, d296559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289388, d296559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94212 q ha hb
  have h2 (q : Pattern) (ha : d287735 q = 1) (hb : d289389 q = 1) : d296560 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289389, d296560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289389, d296560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287735 q = 1) (hb : d289390 q = 1) : d296561 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289390, d296561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289390, d296561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287735 q = 1) (hb : d289391 q = 1) : d296562 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289391, d296562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289391, d296562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287735 q = 1) (hb : d289392 q = 1) : d296563 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289392, d296563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289392, d296563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287735 q = 1) (hb : d289393 q = 1) : d296564 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289393, d296564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289393, d296564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94214 (p : Pattern) (ha : d40759 p = 1) (hb : d287735 p = 1) : d296566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40152 q = 1) (hb : d287735 q = 1) : d296091 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94127 q ha hb
    | true =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40153 q = 1) (hb : d287735 q = 1) : d296092 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d287735 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40154 q = 1) (hb : d287735 q = 1) : d296093 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40154, d296093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d287735 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40155 q = 1) (hb : d287735 q = 1) : d296094 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40155, d296094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40155, d296094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40156 q = 1) (hb : d287735 q = 1) : d296095 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40156, d296095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40156, d296095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40759 q = 1) (hb : d287735 q = 1) : d296566 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40759, d296566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40759, d296566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94215 (p : Pattern) (ha : d40765 p = 1) (hb : d287735 p = 1) : d296572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40504 q = 1) (hb : d287735 q = 1) : d296391 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40504, d296391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94187 q ha hb
    | true =>
      simp only [d40504, d296391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40505 q = 1) (hb : d287735 q = 1) : d296392 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40505, d296392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40505, d296392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40506 q = 1) (hb : d287735 q = 1) : d296393 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40506, d296393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40506, d296393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40507 q = 1) (hb : d287735 q = 1) : d296394 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40507, d296394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40507, d296394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40509 q = 1) (hb : d287735 q = 1) : d296396 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40509, d296396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94188 q ha hb
    | true =>
      simp only [d40509, d296396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40510 q = 1) (hb : d287735 q = 1) : d296397 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40510, d296397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40510, d296397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40511 q = 1) (hb : d287735 q = 1) : d296398 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40511, d296398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40511, d296398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40512 q = 1) (hb : d287735 q = 1) : d296399 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40512, d296399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40512, d296399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40513 q = 1) (hb : d287735 q = 1) : d296400 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40513, d296400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40513, d296400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40517 q = 1) (hb : d287735 q = 1) : d296404 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40517, d296404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94189 q ha hb
    | true =>
      simp only [d40517, d296404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40518 q = 1) (hb : d287735 q = 1) : d296405 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40518, d296405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40518, d296405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40519 q = 1) (hb : d287735 q = 1) : d296406 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40519, d296406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40519, d296406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40520 q = 1) (hb : d287735 q = 1) : d296407 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40520, d296407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40520, d296407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d40760 q = 1) (hb : d287735 q = 1) : d296567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94214 q ha hb
    | true =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d40761 q = 1) (hb : d287735 q = 1) : d296568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40762 q = 1) (hb : d287735 q = 1) : d296569 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40762, d296569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40762, d296569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40763 q = 1) (hb : d287735 q = 1) : d296570 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40763, d296570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40763, d296570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40764 q = 1) (hb : d287735 q = 1) : d296571 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40764, d296571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40764, d296571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40765 q = 1) (hb : d287735 q = 1) : d296572 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40765, d296572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40765, d296572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro94216 (p : Pattern) (ha : d40768 p = 1) (hb : d287735 p = 1) : d296575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40271 q = 1) (hb : d287735 q = 1) : d296209 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40271, d296209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94147 q ha hb
    | true =>
      simp only [d40271, d296209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40272 q = 1) (hb : d287735 q = 1) : d296210 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40272, d296210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40272, d296210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40273 q = 1) (hb : d287735 q = 1) : d296211 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40273, d296211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40273, d296211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40274 q = 1) (hb : d287735 q = 1) : d296212 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40274, d296212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40274, d296212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40760 q = 1) (hb : d287735 q = 1) : d296567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94214 q ha hb
    | true =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40761 q = 1) (hb : d287735 q = 1) : d296568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40762 q = 1) (hb : d287735 q = 1) : d296569 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40762, d296569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40762, d296569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40763 q = 1) (hb : d287735 q = 1) : d296570 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40763, d296570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40763, d296570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40766 q = 1) (hb : d287735 q = 1) : d296573 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40766, d296573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40766, d296573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40767 q = 1) (hb : d287735 q = 1) : d296574 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40767, d296574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40767, d296574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40768 q = 1) (hb : d287735 q = 1) : d296575 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40768, d296575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40768, d296575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94217 (p : Pattern) (ha : d40772 p = 1) (hb : d287735 p = 1) : d296579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40760 q = 1) (hb : d287735 q = 1) : d296567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94214 q ha hb
    | true =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40761 q = 1) (hb : d287735 q = 1) : d296568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40762 q = 1) (hb : d287735 q = 1) : d296569 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40762, d296569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40762, d296569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40763 q = 1) (hb : d287735 q = 1) : d296570 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40763, d296570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40763, d296570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40767 q = 1) (hb : d287735 q = 1) : d296574 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40767, d296574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40767, d296574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40772 q = 1) (hb : d287735 q = 1) : d296579 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40772, d296579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40772, d296579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94218 (p : Pattern) (ha : d40779 p = 1) (hb : d287735 p = 1) : d296586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40769 q = 1) (hb : d287735 q = 1) : d296576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40769, d296576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94215 q ha hb
    | true =>
      simp only [d40769, d296576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94216 q ha hb
  have h2 (q : Pattern) (ha : d40770 q = 1) (hb : d287735 q = 1) : d296577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40770, d296577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40770, d296577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40771 q = 1) (hb : d287735 q = 1) : d296578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40771, d296578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40771, d296578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40773 q = 1) (hb : d287735 q = 1) : d296580 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40773, d296580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94216 q ha hb
    | true =>
      simp only [d40773, d296580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94217 q ha hb
  have h5 (q : Pattern) (ha : d40774 q = 1) (hb : d287735 q = 1) : d296581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40774, d296581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40774, d296581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40775 q = 1) (hb : d287735 q = 1) : d296582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40775, d296582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40775, d296582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40776 q = 1) (hb : d287735 q = 1) : d296583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40776, d296583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40776, d296583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40777 q = 1) (hb : d287735 q = 1) : d296584 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40777, d296584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40777, d296584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40778 q = 1) (hb : d287735 q = 1) : d296585 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40778, d296585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40778, d296585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40779 q = 1) (hb : d287735 q = 1) : d296586 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40779, d296586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40779, d296586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro94219 (p : Pattern) (ha : d40783 p = 1) (hb : d287735 p = 1) : d296590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40773 q = 1) (hb : d287735 q = 1) : d296580 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40773, d296580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94216 q ha hb
    | true =>
      simp only [d40773, d296580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94217 q ha hb
  have h2 (q : Pattern) (ha : d40774 q = 1) (hb : d287735 q = 1) : d296581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40774, d296581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40774, d296581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40775 q = 1) (hb : d287735 q = 1) : d296582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40775, d296582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40775, d296582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40777 q = 1) (hb : d287735 q = 1) : d296584 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40777, d296584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40777, d296584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40782 q = 1) (hb : d287735 q = 1) : d296589 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40782, d296589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40782, d296589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40783 q = 1) (hb : d287735 q = 1) : d296590 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40783, d296590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40783, d296590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94220 (p : Pattern) (ha : d40789 p = 1) (hb : d287735 p = 1) : d296596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40780 q = 1) (hb : d287735 q = 1) : d296587 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94218 q ha hb
    | true =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40781 q = 1) (hb : d287735 q = 1) : d296588 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40784 q = 1) (hb : d287735 q = 1) : d296591 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94219 q ha hb
    | true =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40785 q = 1) (hb : d287735 q = 1) : d296592 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40786 q = 1) (hb : d287735 q = 1) : d296593 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40786, d296593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40786, d296593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40787 q = 1) (hb : d287735 q = 1) : d296594 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40787, d296594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40787, d296594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40788 q = 1) (hb : d287735 q = 1) : d296595 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40788, d296595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40788, d296595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40789 q = 1) (hb : d287735 q = 1) : d296596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40789, d296596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40789, d296596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94221 (p : Pattern) (ha : d40793 p = 1) (hb : d287735 p = 1) : d296600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40784 q = 1) (hb : d287735 q = 1) : d296591 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94219 q ha hb
    | true =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40785 q = 1) (hb : d287735 q = 1) : d296592 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40790 q = 1) (hb : d287735 q = 1) : d296597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40790, d296597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40790, d296597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40791 q = 1) (hb : d287735 q = 1) : d296598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40791, d296598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40791, d296598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40792 q = 1) (hb : d287735 q = 1) : d296599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40792, d296599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40792, d296599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40793 q = 1) (hb : d287735 q = 1) : d296600 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40793, d296600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40793, d296600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94222 (p : Pattern) (ha : d40799 p = 1) (hb : d287735 p = 1) : d296606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40794 q = 1) (hb : d287735 q = 1) : d296601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40794, d296601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94220 q ha hb
    | true =>
      simp only [d40794, d296601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94221 q ha hb
  have h2 (q : Pattern) (ha : d40795 q = 1) (hb : d287735 q = 1) : d296602 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40795, d296602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40795, d296602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40796 q = 1) (hb : d287735 q = 1) : d296603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40796, d296603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40796, d296603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40797 q = 1) (hb : d287735 q = 1) : d296604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40797, d296604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40797, d296604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40798 q = 1) (hb : d287735 q = 1) : d296605 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40798, d296605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40798, d296605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40799 q = 1) (hb : d287735 q = 1) : d296606 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40799, d296606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40799, d296606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94223 (p : Pattern) (ha : d40802 p = 1) (hb : d287735 p = 1) : d296609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40780 q = 1) (hb : d287735 q = 1) : d296587 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94218 q ha hb
    | true =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40781 q = 1) (hb : d287735 q = 1) : d296588 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40784 q = 1) (hb : d287735 q = 1) : d296591 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94219 q ha hb
    | true =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40785 q = 1) (hb : d287735 q = 1) : d296592 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40786 q = 1) (hb : d287735 q = 1) : d296593 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40786, d296593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40786, d296593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40787 q = 1) (hb : d287735 q = 1) : d296594 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40787, d296594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40787, d296594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40788 q = 1) (hb : d287735 q = 1) : d296595 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40788, d296595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40788, d296595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40802 q = 1) (hb : d287735 q = 1) : d296609 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40802, d296609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40802, d296609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94224 (p : Pattern) (ha : d40803 p = 1) (hb : d287735 p = 1) : d296610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40784 q = 1) (hb : d287735 q = 1) : d296591 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94219 q ha hb
    | true =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40785 q = 1) (hb : d287735 q = 1) : d296592 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40790 q = 1) (hb : d287735 q = 1) : d296597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40790, d296597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40790, d296597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40791 q = 1) (hb : d287735 q = 1) : d296598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40791, d296598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40791, d296598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40792 q = 1) (hb : d287735 q = 1) : d296599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40792, d296599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40792, d296599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40803 q = 1) (hb : d287735 q = 1) : d296610 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40803, d296610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40803, d296610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94225 (p : Pattern) (ha : d40809 p = 1) (hb : d287735 p = 1) : d296616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40794 q = 1) (hb : d287735 q = 1) : d296601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40794, d296601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94220 q ha hb
    | true =>
      simp only [d40794, d296601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94221 q ha hb
  have h2 (q : Pattern) (ha : d40795 q = 1) (hb : d287735 q = 1) : d296602 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40795, d296602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40795, d296602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40796 q = 1) (hb : d287735 q = 1) : d296603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40796, d296603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40796, d296603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40797 q = 1) (hb : d287735 q = 1) : d296604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40797, d296604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40797, d296604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40798 q = 1) (hb : d287735 q = 1) : d296605 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40798, d296605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40798, d296605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40804 q = 1) (hb : d287735 q = 1) : d296611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40804, d296611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94223 q ha hb
    | true =>
      simp only [d40804, d296611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94224 q ha hb
  have h7 (q : Pattern) (ha : d40805 q = 1) (hb : d287735 q = 1) : d296612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40805, d296612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40805, d296612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40806 q = 1) (hb : d287735 q = 1) : d296613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40806, d296613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40806, d296613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40807 q = 1) (hb : d287735 q = 1) : d296614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40807, d296614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40807, d296614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40808 q = 1) (hb : d287735 q = 1) : d296615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40808, d296615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40808, d296615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40809 q = 1) (hb : d287735 q = 1) : d296616 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40809, d296616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40809, d296616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94226 (p : Pattern) (ha : d40989 p = 1) (hb : d287735 p = 1) : d296722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40794 q = 1) (hb : d287735 q = 1) : d296601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40794, d296601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94220 q ha hb
    | true =>
      simp only [d40794, d296601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94221 q ha hb
  have h2 (q : Pattern) (ha : d40795 q = 1) (hb : d287735 q = 1) : d296602 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40795, d296602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40795, d296602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40796 q = 1) (hb : d287735 q = 1) : d296603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40796, d296603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40796, d296603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40797 q = 1) (hb : d287735 q = 1) : d296604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40797, d296604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40797, d296604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40798 q = 1) (hb : d287735 q = 1) : d296605 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40798, d296605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40798, d296605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40984 q = 1) (hb : d287735 q = 1) : d296717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40984, d296717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94221 q ha hb
    | true =>
      simp only [d40984, d296717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40985 q = 1) (hb : d287735 q = 1) : d296718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40985, d296718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40985, d296718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40986 q = 1) (hb : d287735 q = 1) : d296719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40986, d296719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40986, d296719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40987 q = 1) (hb : d287735 q = 1) : d296720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40987, d296720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40987, d296720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40988 q = 1) (hb : d287735 q = 1) : d296721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40988, d296721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40988, d296721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40989 q = 1) (hb : d287735 q = 1) : d296722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40989, d296722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40989, d296722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94227 (p : Pattern) (ha : d40995 p = 1) (hb : d287735 p = 1) : d296728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40984 q = 1) (hb : d287735 q = 1) : d296717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40984, d296717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94221 q ha hb
    | true =>
      simp only [d40984, d296717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40985 q = 1) (hb : d287735 q = 1) : d296718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40985, d296718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40985, d296718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40986 q = 1) (hb : d287735 q = 1) : d296719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40986, d296719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40986, d296719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40987 q = 1) (hb : d287735 q = 1) : d296720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40987, d296720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40987, d296720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40988 q = 1) (hb : d287735 q = 1) : d296721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40988, d296721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40988, d296721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40990 q = 1) (hb : d287735 q = 1) : d296723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40990, d296723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94224 q ha hb
    | true =>
      simp only [d40990, d296723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40991 q = 1) (hb : d287735 q = 1) : d296724 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40991, d296724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40991, d296724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40992 q = 1) (hb : d287735 q = 1) : d296725 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40992, d296725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40992, d296725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40993 q = 1) (hb : d287735 q = 1) : d296726 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40993, d296726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40993, d296726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40994 q = 1) (hb : d287735 q = 1) : d296727 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40994, d296727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40994, d296727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40995 q = 1) (hb : d287735 q = 1) : d296728 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40995, d296728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40995, d296728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94228 (p : Pattern) (ha : d41004 p = 1) (hb : d287735 p = 1) : d296737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40990 q = 1) (hb : d287735 q = 1) : d296723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40990, d296723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94224 q ha hb
    | true =>
      simp only [d40990, d296723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40991 q = 1) (hb : d287735 q = 1) : d296724 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40991, d296724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40991, d296724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40992 q = 1) (hb : d287735 q = 1) : d296725 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40992, d296725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40992, d296725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40993 q = 1) (hb : d287735 q = 1) : d296726 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40993, d296726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40993, d296726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40994 q = 1) (hb : d287735 q = 1) : d296727 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40994, d296727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40994, d296727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41004 q = 1) (hb : d287735 q = 1) : d296737 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d41004, d296737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41004, d296737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94229 (p : Pattern) (ha : d41041 p = 1) (hb : d287735 p = 1) : d296774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40372 q = 1) (hb : d287735 q = 1) : d296280 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40372, d296280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40372, d296280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94147 q ha hb
  have h2 (q : Pattern) (ha : d40271 q = 1) (hb : d287735 q = 1) : d296209 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40271, d296209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94147 q ha hb
    | true =>
      simp only [d40271, d296209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40373 q = 1) (hb : d287735 q = 1) : d296281 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40373, d296281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40373, d296281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40272 q = 1) (hb : d287735 q = 1) : d296210 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40272, d296210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40272, d296210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40374 q = 1) (hb : d287735 q = 1) : d296282 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40374, d296282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40374, d296282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40375 q = 1) (hb : d287735 q = 1) : d296283 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40375, d296283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40375, d296283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41025 q = 1) (hb : d287735 q = 1) : d296758 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41025, d296758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41025, d296758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94214 q ha hb
  have h8 (q : Pattern) (ha : d40760 q = 1) (hb : d287735 q = 1) : d296567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94214 q ha hb
    | true =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d41026 q = 1) (hb : d287735 q = 1) : d296759 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41026, d296759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d41026, d296759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40761 q = 1) (hb : d287735 q = 1) : d296568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d41027 q = 1) (hb : d287735 q = 1) : d296760 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41027, d296760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41027, d296760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d41028 q = 1) (hb : d287735 q = 1) : d296761 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41028, d296761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d41028, d296761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d41040 q = 1) (hb : d287735 q = 1) : d296773 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d41040, d296773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41040, d296773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d41034 q = 1) (hb : d287735 q = 1) : d296767 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d41034, d296767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d41034, d296767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d41041 q = 1) (hb : d287735 q = 1) : d296774 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d41041, d296774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d41041, d296774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94230 (p : Pattern) (ha : d41045 p = 1) (hb : d287735 p = 1) : d296778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41025 q = 1) (hb : d287735 q = 1) : d296758 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41025, d296758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41025, d296758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94214 q ha hb
  have h2 (q : Pattern) (ha : d40760 q = 1) (hb : d287735 q = 1) : d296567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94214 q ha hb
    | true =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d41026 q = 1) (hb : d287735 q = 1) : d296759 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41026, d296759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41026, d296759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40761 q = 1) (hb : d287735 q = 1) : d296568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41027 q = 1) (hb : d287735 q = 1) : d296760 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41027, d296760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41027, d296760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41028 q = 1) (hb : d287735 q = 1) : d296761 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41028, d296761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41028, d296761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41034 q = 1) (hb : d287735 q = 1) : d296767 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d41034, d296767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41034, d296767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d41045 q = 1) (hb : d287735 q = 1) : d296778 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d41045, d296778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d41045, d296778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro94231 (p : Pattern) (ha : d41064 p = 1) (hb : d287735 p = 1) : d296797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41046 q = 1) (hb : d287735 q = 1) : d296779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d41046, d296779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94229 q ha hb
    | true =>
      simp only [d41046, d296779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94230 q ha hb
  have h2 (q : Pattern) (ha : d41047 q = 1) (hb : d287735 q = 1) : d296780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d41047, d296780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41047, d296780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d41048 q = 1) (hb : d287735 q = 1) : d296781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d41048, d296781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41048, d296781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d41054 q = 1) (hb : d287735 q = 1) : d296787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d41054, d296787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41054, d296787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41063 q = 1) (hb : d287735 q = 1) : d296796 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d41063, d296796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41063, d296796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d41064 q = 1) (hb : d287735 q = 1) : d296797 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d41064, d296797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41064, d296797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94232 (p : Pattern) (ha : d41135 p = 1) (hb : d287735 p = 1) : d296820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41065 q = 1) (hb : d287735 q = 1) : d296798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d41065, d296798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94231 q ha hb
    | true =>
      simp only [d41065, d296798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d41066 q = 1) (hb : d287735 q = 1) : d296799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d41066, d296799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41066, d296799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d41132 q = 1) (hb : d287735 q = 1) : d296817 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d41132, d296817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41132, d296817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41133 q = 1) (hb : d287735 q = 1) : d296818 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d41133, d296818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41133, d296818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41134 q = 1) (hb : d287735 q = 1) : d296819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41134, d296819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41134, d296819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d41135 q = 1) (hb : d287735 q = 1) : d296820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d41135, d296820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41135, d296820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro94233 (p : Pattern) (ha : d41141 p = 1) (hb : d287735 p = 1) : d296826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41136 q = 1) (hb : d287735 q = 1) : d296821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d41136, d296821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94232 q ha hb
    | true =>
      simp only [d41136, d296821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d41137 q = 1) (hb : d287735 q = 1) : d296822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d41137, d296822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41137, d296822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d41138 q = 1) (hb : d287735 q = 1) : d296823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d41138, d296823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41138, d296823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41139 q = 1) (hb : d287735 q = 1) : d296824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d41139, d296824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41139, d296824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d41140 q = 1) (hb : d287735 q = 1) : d296825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d41140, d296825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41140, d296825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41141 q = 1) (hb : d287735 q = 1) : d296826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d41141, d296826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41141, d296826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94234 (p : Pattern) (ha : d40814 p = 1) (hb : d287735 p = 1) : d296621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40780 q = 1) (hb : d287735 q = 1) : d296587 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94218 q ha hb
    | true =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40781 q = 1) (hb : d287735 q = 1) : d296588 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40784 q = 1) (hb : d287735 q = 1) : d296591 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94219 q ha hb
    | true =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40785 q = 1) (hb : d287735 q = 1) : d296592 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40786 q = 1) (hb : d287735 q = 1) : d296593 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40786, d296593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40786, d296593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40787 q = 1) (hb : d287735 q = 1) : d296594 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40787, d296594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40787, d296594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40813 q = 1) (hb : d287735 q = 1) : d296620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40813, d296620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40813, d296620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40814 q = 1) (hb : d287735 q = 1) : d296621 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40814, d296621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40814, d296621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94235 (p : Pattern) (ha : d40816 p = 1) (hb : d287735 p = 1) : d296623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40784 q = 1) (hb : d287735 q = 1) : d296591 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94219 q ha hb
    | true =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40785 q = 1) (hb : d287735 q = 1) : d296592 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40790 q = 1) (hb : d287735 q = 1) : d296597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40790, d296597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40790, d296597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40791 q = 1) (hb : d287735 q = 1) : d296598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40791, d296598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40791, d296598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40815 q = 1) (hb : d287735 q = 1) : d296622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40815, d296622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40815, d296622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40816 q = 1) (hb : d287735 q = 1) : d296623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40816, d296623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40816, d296623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94236 (p : Pattern) (ha : d40823 p = 1) (hb : d287735 p = 1) : d296630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40780 q = 1) (hb : d287735 q = 1) : d296587 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94218 q ha hb
    | true =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40781 q = 1) (hb : d287735 q = 1) : d296588 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40784 q = 1) (hb : d287735 q = 1) : d296591 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94219 q ha hb
    | true =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40785 q = 1) (hb : d287735 q = 1) : d296592 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40786 q = 1) (hb : d287735 q = 1) : d296593 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40786, d296593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40786, d296593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40821 q = 1) (hb : d287735 q = 1) : d296628 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40821, d296628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40821, d296628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40822 q = 1) (hb : d287735 q = 1) : d296629 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40822, d296629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40822, d296629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40823 q = 1) (hb : d287735 q = 1) : d296630 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40823, d296630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40823, d296630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94237 (p : Pattern) (ha : d40826 p = 1) (hb : d287735 p = 1) : d296633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40784 q = 1) (hb : d287735 q = 1) : d296591 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94219 q ha hb
    | true =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40785 q = 1) (hb : d287735 q = 1) : d296592 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40790 q = 1) (hb : d287735 q = 1) : d296597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40790, d296597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40790, d296597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40824 q = 1) (hb : d287735 q = 1) : d296631 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40824, d296631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40824, d296631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40825 q = 1) (hb : d287735 q = 1) : d296632 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40825, d296632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40825, d296632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40826 q = 1) (hb : d287735 q = 1) : d296633 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40826, d296633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40826, d296633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94238 (p : Pattern) (ha : d40830 p = 1) (hb : d287735 p = 1) : d32687 p = 1 := by
  have h0 (q : Pattern) (ha : d1999 q = 1) (hb : d253269 q = 1) : d1999 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40491 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40830 q = 1) (hb : d287735 q = 1) : d32687 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d40830, d287735, d32687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40830, d287735, d32687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro94239 (p : Pattern) (ha : d40836 p = 1) (hb : d287735 p = 1) : d296638 p = 1 := by
  have h0 (q : Pattern) (ha : d40835 q = 1) (hb : d253269 q = 1) : d40835 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9579 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40836 q = 1) (hb : d287735 q = 1) : d296638 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d40836, d287735, d296638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40836, d287735, d296638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro94240 (p : Pattern) (ha : d40845 p = 1) (hb : d287735 p = 1) : d296647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40831 q = 1) (hb : d287735 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40831, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94238 q ha hb
    | true =>
      simp only [d40831, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40832 q = 1) (hb : d287735 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40832, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40832, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40493 q = 1) (hb : d287735 q = 1) : d296381 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40493, d296381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94185 q ha hb
    | true =>
      simp only [d40493, d296381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40494 q = 1) (hb : d287735 q = 1) : d296382 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40494, d296382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40494, d296382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40833 q = 1) (hb : d287735 q = 1) : d296637 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40833, d296637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40833, d296637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32703 q = 1) (hb : d287735 q = 1) : d32703 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40837 q = 1) (hb : d287735 q = 1) : d296639 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40837, d296639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94239 q ha hb
    | true =>
      simp only [d40837, d296639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40838 q = 1) (hb : d287735 q = 1) : d296640 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40838, d296640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40838, d296640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40839 q = 1) (hb : d287735 q = 1) : d296641 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40839, d296641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40839, d296641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40840 q = 1) (hb : d287735 q = 1) : d296642 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40840, d296642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40840, d296642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40841 q = 1) (hb : d287735 q = 1) : d296643 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40841, d296643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40841, d296643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40265 q = 1) (hb : d287735 q = 1) : d296203 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94146 q ha hb
    | true =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40266 q = 1) (hb : d287735 q = 1) : d296204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d40495 q = 1) (hb : d287735 q = 1) : d296383 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40495, d296383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40495, d296383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d40152 q = 1) (hb : d287735 q = 1) : d296091 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94127 q ha hb
    | true =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40153 q = 1) (hb : d287735 q = 1) : d296092 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d40842 q = 1) (hb : d287735 q = 1) : d296644 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40842, d296644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40842, d296644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d40843 q = 1) (hb : d287735 q = 1) : d296645 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40843, d296645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40843, d296645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40844 q = 1) (hb : d287735 q = 1) : d296646 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40844, d296646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d40844, d296646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d40845 q = 1) (hb : d287735 q = 1) : d296647 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40845, d296647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40845, d296647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro94241 (p : Pattern) (ha : d40850 p = 1) (hb : d287735 p = 1) : d296652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40493 q = 1) (hb : d287735 q = 1) : d296381 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40493, d296381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94185 q ha hb
    | true =>
      simp only [d40493, d296381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40494 q = 1) (hb : d287735 q = 1) : d296382 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40494, d296382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40494, d296382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40265 q = 1) (hb : d287735 q = 1) : d296203 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94146 q ha hb
    | true =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40266 q = 1) (hb : d287735 q = 1) : d296204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40495 q = 1) (hb : d287735 q = 1) : d296383 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40495, d296383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40495, d296383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40498 q = 1) (hb : d287735 q = 1) : d296385 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40498, d296385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94186 q ha hb
    | true =>
      simp only [d40498, d296385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40499 q = 1) (hb : d287735 q = 1) : d296386 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40499, d296386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40499, d296386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40152 q = 1) (hb : d287735 q = 1) : d296091 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94127 q ha hb
    | true =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40153 q = 1) (hb : d287735 q = 1) : d296092 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40500 q = 1) (hb : d287735 q = 1) : d296387 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40500, d296387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40500, d296387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40501 q = 1) (hb : d287735 q = 1) : d296388 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40501, d296388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40501, d296388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40502 q = 1) (hb : d287735 q = 1) : d296389 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40502, d296389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40502, d296389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40267 q = 1) (hb : d287735 q = 1) : d296205 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d40514 q = 1) (hb : d287735 q = 1) : d296401 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40514, d296401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40514, d296401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d40515 q = 1) (hb : d287735 q = 1) : d296402 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40515, d296402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40515, d296402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40850 q = 1) (hb : d287735 q = 1) : d296652 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40850, d296652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40850, d296652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro94242 (p : Pattern) (ha : d40858 p = 1) (hb : d287735 p = 1) : d296660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40493 q = 1) (hb : d287735 q = 1) : d296381 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40493, d296381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94185 q ha hb
    | true =>
      simp only [d40493, d296381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40494 q = 1) (hb : d287735 q = 1) : d296382 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40494, d296382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40494, d296382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40265 q = 1) (hb : d287735 q = 1) : d296203 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94146 q ha hb
    | true =>
      simp only [d40265, d296203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40266 q = 1) (hb : d287735 q = 1) : d296204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40266, d296204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40495 q = 1) (hb : d287735 q = 1) : d296383 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40495, d296383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40495, d296383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40856 q = 1) (hb : d287735 q = 1) : d296658 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40856, d296658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40856, d296658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40857 q = 1) (hb : d287735 q = 1) : d296659 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40857, d296659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40857, d296659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40152 q = 1) (hb : d287735 q = 1) : d296091 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94127 q ha hb
    | true =>
      simp only [d40152, d296091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40153 q = 1) (hb : d287735 q = 1) : d296092 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40153, d296092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40267 q = 1) (hb : d287735 q = 1) : d296205 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40267, d296205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40514 q = 1) (hb : d287735 q = 1) : d296401 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40514, d296401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40514, d296401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40515 q = 1) (hb : d287735 q = 1) : d296402 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40515, d296402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40515, d296402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40858 q = 1) (hb : d287735 q = 1) : d296660 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40858, d296660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40858, d296660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro94243 (p : Pattern) (ha : d40864 p = 1) (hb : d287735 p = 1) : d296666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40846 q = 1) (hb : d287735 q = 1) : d296648 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40846, d296648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94240 q ha hb
    | true =>
      simp only [d40846, d296648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40847 q = 1) (hb : d287735 q = 1) : d296649 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40847, d296649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40847, d296649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40848 q = 1) (hb : d287735 q = 1) : d296650 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40848, d296650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40848, d296650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40849 q = 1) (hb : d287735 q = 1) : d296651 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40849, d296651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40849, d296651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40851 q = 1) (hb : d287735 q = 1) : d296653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40851, d296653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94241 q ha hb
    | true =>
      simp only [d40851, d296653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40852 q = 1) (hb : d287735 q = 1) : d296654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40852, d296654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40852, d296654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40853 q = 1) (hb : d287735 q = 1) : d296655 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40853, d296655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40853, d296655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40854 q = 1) (hb : d287735 q = 1) : d296656 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40854, d296656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40854, d296656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40855 q = 1) (hb : d287735 q = 1) : d296657 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40855, d296657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40855, d296657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40859 q = 1) (hb : d287735 q = 1) : d296661 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40859, d296661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94242 q ha hb
    | true =>
      simp only [d40859, d296661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40860 q = 1) (hb : d287735 q = 1) : d296662 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40860, d296662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40860, d296662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40861 q = 1) (hb : d287735 q = 1) : d296663 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40861, d296663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40861, d296663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40862 q = 1) (hb : d287735 q = 1) : d296664 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40862, d296664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40862, d296664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d40517 q = 1) (hb : d287735 q = 1) : d296404 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40517, d296404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94189 q ha hb
    | true =>
      simp only [d40517, d296404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d40518 q = 1) (hb : d287735 q = 1) : d296405 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40518, d296405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40518, d296405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40519 q = 1) (hb : d287735 q = 1) : d296406 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40519, d296406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40519, d296406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40520 q = 1) (hb : d287735 q = 1) : d296407 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40520, d296407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40520, d296407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40863 q = 1) (hb : d287735 q = 1) : d296665 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40863, d296665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40863, d296665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40864 q = 1) (hb : d287735 q = 1) : d296666 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40864, d296666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40864, d296666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro94244 (p : Pattern) (ha : d40868 p = 1) (hb : d287735 p = 1) : d296670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40517 q = 1) (hb : d287735 q = 1) : d296404 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40517, d296404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94189 q ha hb
    | true =>
      simp only [d40517, d296404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40518 q = 1) (hb : d287735 q = 1) : d296405 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40518, d296405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40518, d296405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40519 q = 1) (hb : d287735 q = 1) : d296406 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40519, d296406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40519, d296406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40520 q = 1) (hb : d287735 q = 1) : d296407 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40520, d296407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40520, d296407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40760 q = 1) (hb : d287735 q = 1) : d296567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94214 q ha hb
    | true =>
      simp only [d40760, d296567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40761 q = 1) (hb : d287735 q = 1) : d296568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40761, d296568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40762 q = 1) (hb : d287735 q = 1) : d296569 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40762, d296569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40762, d296569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40763 q = 1) (hb : d287735 q = 1) : d296570 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40763, d296570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40763, d296570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40764 q = 1) (hb : d287735 q = 1) : d296571 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40764, d296571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40764, d296571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40767 q = 1) (hb : d287735 q = 1) : d296574 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40767, d296574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40767, d296574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40868 q = 1) (hb : d287735 q = 1) : d296670 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40868, d296670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40868, d296670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro94245 (p : Pattern) (ha : d40874 p = 1) (hb : d287735 p = 1) : d296676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40865 q = 1) (hb : d287735 q = 1) : d296667 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40865, d296667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94243 q ha hb
    | true =>
      simp only [d40865, d296667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94215 q ha hb
  have h2 (q : Pattern) (ha : d40866 q = 1) (hb : d287735 q = 1) : d296668 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40866, d296668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40866, d296668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40867 q = 1) (hb : d287735 q = 1) : d296669 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40867, d296669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40867, d296669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40869 q = 1) (hb : d287735 q = 1) : d296671 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40869, d296671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94215 q ha hb
    | true =>
      simp only [d40869, d296671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94244 q ha hb
  have h5 (q : Pattern) (ha : d40870 q = 1) (hb : d287735 q = 1) : d296672 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40870, d296672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40870, d296672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40871 q = 1) (hb : d287735 q = 1) : d296673 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40871, d296673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40871, d296673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40872 q = 1) (hb : d287735 q = 1) : d296674 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40872, d296674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40872, d296674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40769 q = 1) (hb : d287735 q = 1) : d296576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40769, d296576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94215 q ha hb
    | true =>
      simp only [d40769, d296576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94216 q ha hb
  have h9 (q : Pattern) (ha : d40770 q = 1) (hb : d287735 q = 1) : d296577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40770, d296577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40770, d296577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40771 q = 1) (hb : d287735 q = 1) : d296578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40771, d296578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40771, d296578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40773 q = 1) (hb : d287735 q = 1) : d296580 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40773, d296580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94216 q ha hb
    | true =>
      simp only [d40773, d296580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94217 q ha hb
  have h12 (q : Pattern) (ha : d40774 q = 1) (hb : d287735 q = 1) : d296581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40774, d296581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40774, d296581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40775 q = 1) (hb : d287735 q = 1) : d296582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40775, d296582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40775, d296582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40776 q = 1) (hb : d287735 q = 1) : d296583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40776, d296583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40776, d296583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d40873 q = 1) (hb : d287735 q = 1) : d296675 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40873, d296675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40873, d296675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40874 q = 1) (hb : d287735 q = 1) : d296676 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40874, d296676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d40874, d296676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro94246 (p : Pattern) (ha : d40880 p = 1) (hb : d287735 p = 1) : d296682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40875 q = 1) (hb : d287735 q = 1) : d296677 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40875, d296677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94245 q ha hb
    | true =>
      simp only [d40875, d296677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40876 q = 1) (hb : d287735 q = 1) : d296678 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40876, d296678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40876, d296678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40780 q = 1) (hb : d287735 q = 1) : d296587 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94218 q ha hb
    | true =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40781 q = 1) (hb : d287735 q = 1) : d296588 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40877 q = 1) (hb : d287735 q = 1) : d296679 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40877, d296679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40877, d296679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40878 q = 1) (hb : d287735 q = 1) : d296680 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40878, d296680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40878, d296680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40879 q = 1) (hb : d287735 q = 1) : d296681 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40879, d296681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40879, d296681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40880 q = 1) (hb : d287735 q = 1) : d296682 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40880, d296682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40880, d296682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro94247 (p : Pattern) (ha : d40952 p = 1) (hb : d287735 p = 1) : d296688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40780 q = 1) (hb : d287735 q = 1) : d296587 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94218 q ha hb
    | true =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40781 q = 1) (hb : d287735 q = 1) : d296588 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40949 q = 1) (hb : d287735 q = 1) : d296685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40949, d296685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40949, d296685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40950 q = 1) (hb : d287735 q = 1) : d296686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40950, d296686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40950, d296686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40951 q = 1) (hb : d287735 q = 1) : d296687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40951, d296687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40951, d296687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40952 q = 1) (hb : d287735 q = 1) : d296688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40952, d296688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40952, d296688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro94248 (p : Pattern) (ha : d287735 p = 1) (hb : d289399 p = 1) : d296694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40817 q = 1) (hb : d287735 q = 1) : d296624 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40817, d296624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94234 q ha hb
    | true =>
      simp only [d40817, d296624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94235 q ha hb
  have h2 (q : Pattern) (ha : d40818 q = 1) (hb : d287735 q = 1) : d296625 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40818, d296625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40818, d296625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40819 q = 1) (hb : d287735 q = 1) : d296626 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40819, d296626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40819, d296626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40820 q = 1) (hb : d287735 q = 1) : d296627 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40820, d296627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40820, d296627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40827 q = 1) (hb : d287735 q = 1) : d296634 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40827, d296634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94236 q ha hb
    | true =>
      simp only [d40827, d296634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94237 q ha hb
  have h6 (q : Pattern) (ha : d40828 q = 1) (hb : d287735 q = 1) : d296635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40828, d296635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40828, d296635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40829 q = 1) (hb : d287735 q = 1) : d296636 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40829, d296636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40829, d296636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40881 q = 1) (hb : d287735 q = 1) : d296683 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40881, d296683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94246 q ha hb
    | true =>
      simp only [d40881, d296683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94220 q ha hb
  have h9 (q : Pattern) (ha : d287735 q = 1) (hb : d289395 q = 1) : d296684 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289395, d296684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d289395, d296684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d40953 q = 1) (hb : d287735 q = 1) : d296689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40953, d296689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94247 q ha hb
    | true =>
      simp only [d40953, d296689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40954 q = 1) (hb : d287735 q = 1) : d296690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40954, d296690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40954, d296690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d287735 q = 1) (hb : d289396 q = 1) : d296691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289396, d296691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289396, d296691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d287735 q = 1) (hb : d289397 q = 1) : d296692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289397, d296692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d289397, d296692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d287735 q = 1) (hb : d289398 q = 1) : d296693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289398, d296693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289398, d296693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d287735 q = 1) (hb : d289399 q = 1) : d296694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289399, d296694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289399, d296694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro94249 (p : Pattern) (ha : d40959 p = 1) (hb : d287735 p = 1) : d296695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40780 q = 1) (hb : d287735 q = 1) : d296587 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94218 q ha hb
    | true =>
      simp only [d40780, d296587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40781 q = 1) (hb : d287735 q = 1) : d296588 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40781, d296588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40784 q = 1) (hb : d287735 q = 1) : d296591 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94219 q ha hb
    | true =>
      simp only [d40784, d296591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40785 q = 1) (hb : d287735 q = 1) : d296592 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40785, d296592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40786 q = 1) (hb : d287735 q = 1) : d296593 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40786, d296593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40786, d296593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40787 q = 1) (hb : d287735 q = 1) : d296594 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40787, d296594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40787, d296594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40813 q = 1) (hb : d287735 q = 1) : d296620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40813, d296620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40813, d296620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40959 q = 1) (hb : d287735 q = 1) : d296695 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40959, d296695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40959, d296695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
