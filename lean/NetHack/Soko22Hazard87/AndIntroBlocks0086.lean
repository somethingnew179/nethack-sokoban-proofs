import NetHack.Soko22Hazard87.AndIntroBlocks0085
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro21500 (p : Pattern) (ha : d8602 p = 1) (hb : d92314 p = 1) : d93515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8578 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8579 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8580 q = 1) (hb : d92314 q = 1) : d8639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8580, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8601 q = 1) (hb : d92314 q = 1) : d93514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8602 q = 1) (hb : d92314 q = 1) : d93515 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8602, d93515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8602, d93515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21501 (p : Pattern) (ha : d8609 p = 1) (hb : d92314 p = 1) : d93522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8578 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8579 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8607 q = 1) (hb : d92314 q = 1) : d93520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8608 q = 1) (hb : d92314 q = 1) : d93521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8608, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8609 q = 1) (hb : d92314 q = 1) : d93522 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8609, d93522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8609, d93522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21502 (p : Pattern) (ha : d8621 p = 1) (hb : d92314 p = 1) : d93529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8617 q = 1) (hb : d92313 q = 1) : d8617 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6879 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8618 q = 1) (hb : d92314 q = 1) : d93526 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, d92314, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8618, d92314, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8619 q = 1) (hb : d92314 q = 1) : d93527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8619, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8620 q = 1) (hb : d92314 q = 1) : d93528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8620, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8621 q = 1) (hb : d92314 q = 1) : d93529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8621, d93529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8621, d93529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21503 (p : Pattern) (ha : d92314 p = 1) (hb : d94308 p = 1) : d93539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d92314 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8603 q = 1) (hb : d92314 q = 1) : d93516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21500 q ha hb
    | true =>
      simp only [d8603, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8604 q = 1) (hb : d92314 q = 1) : d93517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8605 q = 1) (hb : d92314 q = 1) : d93518 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8605, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8606 q = 1) (hb : d92314 q = 1) : d93519 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d92314 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8610 q = 1) (hb : d92314 q = 1) : d93523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21501 q ha hb
    | true =>
      simp only [d8610, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8611 q = 1) (hb : d92314 q = 1) : d93524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8612 q = 1) (hb : d92314 q = 1) : d93525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8612, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8626 q = 1) (hb : d92314 q = 1) : d93534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21502 q ha hb
    | true =>
      simp only [d8626, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21498 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94304 q = 1) : d93535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94304, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8643 q = 1) (hb : d92314 q = 1) : d8643 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94305 q = 1) : d93536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94305, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94306 q = 1) : d93537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94306, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94307 q = 1) : d93538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94307, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94308 q = 1) : d93539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94308, d93539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94308, d93539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21504 (p : Pattern) (ha : d8648 p = 1) (hb : d92314 p = 1) : d93540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8578 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8579 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8580 q = 1) (hb : d92314 q = 1) : d8639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8580, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8601 q = 1) (hb : d92314 q = 1) : d93514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8648 q = 1) (hb : d92314 q = 1) : d93540 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8648, d93540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8648, d93540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21505 (p : Pattern) (ha : d8653 p = 1) (hb : d92314 p = 1) : d93545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8578 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8579 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8579, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8607 q = 1) (hb : d92314 q = 1) : d93520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8608 q = 1) (hb : d92314 q = 1) : d93521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8608, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8653 q = 1) (hb : d92314 q = 1) : d93545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8653, d93545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8653, d93545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21506 (p : Pattern) (ha : d8657 p = 1) (hb : d92314 p = 1) : d93549 p = 1 := by
  have h0 (q : Pattern) (ha : d8617 q = 1) (hb : d92313 q = 1) : d8617 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6879 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8618 q = 1) (hb : d92314 q = 1) : d93526 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, d92314, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8618, d92314, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8619 q = 1) (hb : d92314 q = 1) : d93527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8619, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8620 q = 1) (hb : d92314 q = 1) : d93528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8620, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8657 q = 1) (hb : d92314 q = 1) : d93549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8657, d93549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8657, d93549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21507 (p : Pattern) (ha : d8658 p = 1) (hb : d92314 p = 1) : d93550 p = 1 := by
  have h0 (q : Pattern) (ha : d6879 q = 1) (hb : d92313 q = 1) : d6879 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8622 q = 1) (hb : d92314 q = 1) : d93530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d92314, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8622, d92314, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8623 q = 1) (hb : d92314 q = 1) : d93531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8623, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8624 q = 1) (hb : d92314 q = 1) : d93532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8624, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8658 q = 1) (hb : d92314 q = 1) : d93550 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8658, d93550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8658, d93550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21508 (p : Pattern) (ha : d92314 p = 1) (hb : d94313 p = 1) : d93556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d92314 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8603 q = 1) (hb : d92314 q = 1) : d93516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21500 q ha hb
    | true =>
      simp only [d8603, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8604 q = 1) (hb : d92314 q = 1) : d93517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8605 q = 1) (hb : d92314 q = 1) : d93518 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8605, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8606 q = 1) (hb : d92314 q = 1) : d93519 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d92314 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8610 q = 1) (hb : d92314 q = 1) : d93523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21501 q ha hb
    | true =>
      simp only [d8610, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8611 q = 1) (hb : d92314 q = 1) : d93524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8612 q = 1) (hb : d92314 q = 1) : d93525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8612, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8626 q = 1) (hb : d92314 q = 1) : d93534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21502 q ha hb
    | true =>
      simp only [d8626, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21498 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94304 q = 1) : d93535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94304, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8643 q = 1) (hb : d92314 q = 1) : d8643 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94305 q = 1) : d93536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94305, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94306 q = 1) : d93537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94306, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94307 q = 1) : d93538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94307, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d916 q = 1) (hb : d92314 q = 1) : d916 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d8649 q = 1) (hb : d92314 q = 1) : d93541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8649, d93541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21504 q ha hb
    | true =>
      simp only [d8649, d93541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8650 q = 1) (hb : d92314 q = 1) : d93542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8650, d93542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8650, d93542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8651 q = 1) (hb : d92314 q = 1) : d93543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8651, d93543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d8651, d93543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d8652 q = 1) (hb : d92314 q = 1) : d93544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8652, d93544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8652, d93544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d922 q = 1) (hb : d92314 q = 1) : d922 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d8654 q = 1) (hb : d92314 q = 1) : d93546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8654, d93546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21505 q ha hb
    | true =>
      simp only [d8654, d93546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d8655 q = 1) (hb : d92314 q = 1) : d93547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8655, d93547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8655, d93547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8656 q = 1) (hb : d92314 q = 1) : d93548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8656, d93548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d8656, d93548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8659 q = 1) (hb : d92314 q = 1) : d93551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21506 q ha hb
    | true =>
      simp only [d8659, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21507 q ha hb
  have h26 (q : Pattern) (ha : d92314 q = 1) (hb : d94309 q = 1) : d93552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94309, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d8665 q = 1) (hb : d92314 q = 1) : d8665 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d92314 q = 1) (hb : d94310 q = 1) : d93553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d94310, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92314 q = 1) (hb : d94311 q = 1) : d93554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94311, d93554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d94311, d93554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92314 q = 1) (hb : d94312 q = 1) : d93555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94312, d93555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d94312, d93555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92314 q = 1) (hb : d94313 q = 1) : d93556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94313, d93556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94313, d93556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21509 (p : Pattern) (ha : d92314 p = 1) (hb : d94320 p = 1) : d93570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8659 q = 1) (hb : d92314 q = 1) : d93551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21506 q ha hb
    | true =>
      simp only [d8659, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21507 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94309 q = 1) : d93552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94309, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8665 q = 1) (hb : d92314 q = 1) : d8665 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94310 q = 1) : d93553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94310, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94318 q = 1) : d93568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94318, d93568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94318, d93568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94319 q = 1) : d93569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94319, d93569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94319, d93569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94320 q = 1) : d93570 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94320, d93570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94320, d93570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21510 (p : Pattern) (ha : d8697 p = 1) (hb : d92314 p = 1) : d93579 p = 1 := by
  have h0 (q : Pattern) (ha : d8693 q = 1) (hb : d92313 q = 1) : d8693 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8694 q = 1) (hb : d92314 q = 1) : d93576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8694, d92314, d93576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8694, d92314, d93576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8695 q = 1) (hb : d92314 q = 1) : d93577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8695, d93577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8695, d93577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8696 q = 1) (hb : d92314 q = 1) : d93578 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8696, d93578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8696, d93578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8697 q = 1) (hb : d92314 q = 1) : d93579 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8697, d93579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8697, d93579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21511 (p : Pattern) (ha : d8701 p = 1) (hb : d92314 p = 1) : d93583 p = 1 := by
  have h0 (q : Pattern) (ha : d6925 q = 1) (hb : d92313 q = 1) : d6925 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8698 q = 1) (hb : d92314 q = 1) : d93580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8698, d92314, d93580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8698, d92314, d93580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8699 q = 1) (hb : d92314 q = 1) : d93581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8699, d93581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8699, d93581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8700 q = 1) (hb : d92314 q = 1) : d93582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8700, d93582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8700, d93582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8701 q = 1) (hb : d92314 q = 1) : d93583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8701, d93583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8701, d93583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21512 (p : Pattern) (ha : d92314 p = 1) (hb : d94330 p = 1) : d93589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8702 q = 1) (hb : d92314 q = 1) : d93584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8702, d93584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21510 q ha hb
    | true =>
      simp only [d8702, d93584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21511 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94326 q = 1) : d93585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94326, d93585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94326, d93585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8723 q = 1) (hb : d92314 q = 1) : d8723 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94327 q = 1) : d93586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94327, d93586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94327, d93586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94328 q = 1) : d93587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94328, d93587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94328, d93587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94329 q = 1) : d93588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94329, d93588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94329, d93588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94330 q = 1) : d93589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94330, d93589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94330, d93589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21513 (p : Pattern) (ha : d92314 p = 1) (hb : d94336 p = 1) : d93595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8589 q = 1) (hb : d92314 q = 1) : d93503 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8589, d93503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8589, d93503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21495 q ha hb
  have h2 (q : Pattern) (ha : d8590 q = 1) (hb : d92314 q = 1) : d93504 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8590, d93504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8590, d93504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8598 q = 1) (hb : d92314 q = 1) : d93511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21495 q ha hb
    | true =>
      simp only [d8598, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21497 q ha hb
  have h4 (q : Pattern) (ha : d8599 q = 1) (hb : d92314 q = 1) : d93512 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8599, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8600 q = 1) (hb : d92314 q = 1) : d93513 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8600, d93513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8600, d93513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94314 q = 1) : d93557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94314, d93557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21503 q ha hb
    | true =>
      simp only [d94314, d93557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21508 q ha hb
  have h7 (q : Pattern) (ha : d950 q = 1) (hb : d92314 q = 1) : d950 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8677 q = 1) (hb : d92314 q = 1) : d93564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8677, d93564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21499 q ha hb
    | true =>
      simp only [d8677, d93564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94315 q = 1) : d93565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94315, d93565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94315, d93565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94316 q = 1) : d93566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94316, d93566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94316, d93566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94317 q = 1) : d93567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94317, d93567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94317, d93567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94321 q = 1) : d93571 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94321, d93571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94321, d93571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21509 q ha hb
  have h13 (q : Pattern) (ha : d960 q = 1) (hb : d92314 q = 1) : d960 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94322 q = 1) : d93572 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94322, d93572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94322, d93572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94323 q = 1) : d93573 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94323, d93573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94323, d93573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94324 q = 1) : d93574 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94324, d93574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94324, d93574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92314 q = 1) (hb : d94325 q = 1) : d93575 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94325, d93575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94325, d93575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92314 q = 1) (hb : d94331 q = 1) : d93590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94331, d93590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94331, d93590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21512 q ha hb
  have h19 (q : Pattern) (ha : d1070 q = 1) (hb : d92314 q = 1) : d1070 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92314 q = 1) (hb : d94332 q = 1) : d93591 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94332, d93591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94332, d93591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92314 q = 1) (hb : d94333 q = 1) : d93592 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94333, d93592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94333, d93592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92314 q = 1) (hb : d94334 q = 1) : d93593 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94334, d93593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94334, d93593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92314 q = 1) (hb : d94335 q = 1) : d93594 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94335, d93594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94335, d93594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92314 q = 1) (hb : d94336 q = 1) : d93595 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94336, d93595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94336, d93595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro21514 (p : Pattern) (ha : d92314 p = 1) (hb : d94342 p = 1) : d93601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94337 q = 1) : d93596 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94337, d93596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94337, d93596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21513 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94338 q = 1) : d93597 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94338, d93597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94338, d93597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94339 q = 1) : d93598 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94339, d93598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94339, d93598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94340 q = 1) : d93599 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94340, d93599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94340, d93599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94341 q = 1) : d93600 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94341, d93600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94341, d93600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94342 q = 1) : d93601 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94342, d93601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94342, d93601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21515 (p : Pattern) (ha : d8749 p = 1) (hb : d92314 p = 1) : d8808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8745 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8746 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8747 q = 1) (hb : d92314 q = 1) : d8806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8747, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8748 q = 1) (hb : d92314 q = 1) : d8807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8748, d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8749 q = 1) (hb : d92314 q = 1) : d8808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8749, d8808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8749, d8808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21516 (p : Pattern) (ha : d8755 p = 1) (hb : d92314 p = 1) : d93609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92314 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8750 q = 1) (hb : d92314 q = 1) : d93604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21515 q ha hb
    | true =>
      simp only [d8750, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8751 q = 1) (hb : d92314 q = 1) : d93605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8752 q = 1) (hb : d92314 q = 1) : d93606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8752, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8753 q = 1) (hb : d92314 q = 1) : d93607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8754 q = 1) (hb : d92314 q = 1) : d93608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8755 q = 1) (hb : d92314 q = 1) : d93609 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8755, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8755, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21517 (p : Pattern) (ha : d8758 p = 1) (hb : d92314 p = 1) : d8830 p = 1 := by
  have h0 (q : Pattern) (ha : d8745 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8746 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8747 q = 1) (hb : d92314 q = 1) : d8806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8747, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8748 q = 1) (hb : d92314 q = 1) : d8807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8748, d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8758 q = 1) (hb : d92314 q = 1) : d8830 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8758, d8830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8758, d8830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21518 (p : Pattern) (ha : d8764 p = 1) (hb : d92314 p = 1) : d93617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92314 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8750 q = 1) (hb : d92314 q = 1) : d93604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21515 q ha hb
    | true =>
      simp only [d8750, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8751 q = 1) (hb : d92314 q = 1) : d93605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8752 q = 1) (hb : d92314 q = 1) : d93606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8752, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8753 q = 1) (hb : d92314 q = 1) : d93607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8754 q = 1) (hb : d92314 q = 1) : d93608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d92314 q = 1) : d1172 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8759 q = 1) (hb : d92314 q = 1) : d93612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21517 q ha hb
    | true =>
      simp only [d8759, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8760 q = 1) (hb : d92314 q = 1) : d93613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8761 q = 1) (hb : d92314 q = 1) : d93614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8761, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8762 q = 1) (hb : d92314 q = 1) : d93615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8763 q = 1) (hb : d92314 q = 1) : d93616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8764 q = 1) (hb : d92314 q = 1) : d93617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8764, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8764, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21519 (p : Pattern) (ha : d8792 p = 1) (hb : d92314 p = 1) : d93640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6958 q = 1) (hb : d92313 q = 1) : d6958 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8789 q = 1) (hb : d92314 q = 1) : d93637 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d92314, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8789, d92314, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8790 q = 1) (hb : d92314 q = 1) : d93638 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8790, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8791 q = 1) (hb : d92314 q = 1) : d93639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8791, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8792 q = 1) (hb : d92314 q = 1) : d93640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8792, d93640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8792, d93640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21520 (p : Pattern) (ha : d8843 p = 1) (hb : d92314 p = 1) : d93670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92314 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8838 q = 1) (hb : d92314 q = 1) : d93665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8838, d93665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21519 q ha hb
    | true =>
      simp only [d8838, d93665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8839 q = 1) (hb : d92314 q = 1) : d93666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8839, d93666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8839, d93666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8840 q = 1) (hb : d92314 q = 1) : d93667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8840, d93667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8840, d93667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8841 q = 1) (hb : d92314 q = 1) : d93668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8841, d93668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8841, d93668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8842 q = 1) (hb : d92314 q = 1) : d93669 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8842, d93669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8842, d93669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1354 q = 1) (hb : d92314 q = 1) : d1354 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8843 q = 1) (hb : d92314 q = 1) : d93670 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8843, d93670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8843, d93670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21521 (p : Pattern) (ha : d8769 p = 1) (hb : d92314 p = 1) : d93622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8745 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8746 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8747 q = 1) (hb : d92314 q = 1) : d8806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8747, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8768 q = 1) (hb : d92314 q = 1) : d93621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8769 q = 1) (hb : d92314 q = 1) : d93622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8769, d93622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8769, d93622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21522 (p : Pattern) (ha : d8776 p = 1) (hb : d92314 p = 1) : d93629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8745 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8746 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8774 q = 1) (hb : d92314 q = 1) : d93627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8775 q = 1) (hb : d92314 q = 1) : d93628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8775, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8776 q = 1) (hb : d92314 q = 1) : d93629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8776, d93629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8776, d93629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21523 (p : Pattern) (ha : d8788 p = 1) (hb : d92314 p = 1) : d93636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8784 q = 1) (hb : d92313 q = 1) : d8784 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6958 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8785 q = 1) (hb : d92314 q = 1) : d93633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d92314, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8785, d92314, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8786 q = 1) (hb : d92314 q = 1) : d93634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8786, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8787 q = 1) (hb : d92314 q = 1) : d93635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8787, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8788 q = 1) (hb : d92314 q = 1) : d93636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8788, d93636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8788, d93636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21524 (p : Pattern) (ha : d92314 p = 1) (hb : d94349 p = 1) : d93646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d92314 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8770 q = 1) (hb : d92314 q = 1) : d93623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21521 q ha hb
    | true =>
      simp only [d8770, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8771 q = 1) (hb : d92314 q = 1) : d93624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8772 q = 1) (hb : d92314 q = 1) : d93625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8772, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8773 q = 1) (hb : d92314 q = 1) : d93626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d92314 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8777 q = 1) (hb : d92314 q = 1) : d93630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21522 q ha hb
    | true =>
      simp only [d8777, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8778 q = 1) (hb : d92314 q = 1) : d93631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8779 q = 1) (hb : d92314 q = 1) : d93632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8779, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8793 q = 1) (hb : d92314 q = 1) : d93641 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21523 q ha hb
    | true =>
      simp only [d8793, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21519 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94345 q = 1) : d93642 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94345, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8810 q = 1) (hb : d92314 q = 1) : d8810 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94346 q = 1) : d93643 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94346, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94347 q = 1) : d93644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94347, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94348 q = 1) : d93645 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94348, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94349 q = 1) : d93646 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94349, d93646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94349, d93646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21525 (p : Pattern) (ha : d8815 p = 1) (hb : d92314 p = 1) : d93647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8745 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8746 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8747 q = 1) (hb : d92314 q = 1) : d8806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8747, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8768 q = 1) (hb : d92314 q = 1) : d93621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8815 q = 1) (hb : d92314 q = 1) : d93647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8815, d93647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8815, d93647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21526 (p : Pattern) (ha : d8820 p = 1) (hb : d92314 p = 1) : d93652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8745 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8746 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8746, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8774 q = 1) (hb : d92314 q = 1) : d93627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8775 q = 1) (hb : d92314 q = 1) : d93628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8775, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8820 q = 1) (hb : d92314 q = 1) : d93652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8820, d93652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8820, d93652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21527 (p : Pattern) (ha : d8824 p = 1) (hb : d92314 p = 1) : d93656 p = 1 := by
  have h0 (q : Pattern) (ha : d8784 q = 1) (hb : d92313 q = 1) : d8784 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6958 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8785 q = 1) (hb : d92314 q = 1) : d93633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d92314, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8785, d92314, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8786 q = 1) (hb : d92314 q = 1) : d93634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8786, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8787 q = 1) (hb : d92314 q = 1) : d93635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8787, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8824 q = 1) (hb : d92314 q = 1) : d93656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8824, d93656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8824, d93656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21528 (p : Pattern) (ha : d8825 p = 1) (hb : d92314 p = 1) : d93657 p = 1 := by
  have h0 (q : Pattern) (ha : d6958 q = 1) (hb : d92313 q = 1) : d6958 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8789 q = 1) (hb : d92314 q = 1) : d93637 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d92314, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8789, d92314, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8790 q = 1) (hb : d92314 q = 1) : d93638 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8790, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8791 q = 1) (hb : d92314 q = 1) : d93639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8791, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8825 q = 1) (hb : d92314 q = 1) : d93657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8825, d93657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8825, d93657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21529 (p : Pattern) (ha : d92314 p = 1) (hb : d94354 p = 1) : d93663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d92314 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8770 q = 1) (hb : d92314 q = 1) : d93623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21521 q ha hb
    | true =>
      simp only [d8770, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8771 q = 1) (hb : d92314 q = 1) : d93624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8772 q = 1) (hb : d92314 q = 1) : d93625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8772, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8773 q = 1) (hb : d92314 q = 1) : d93626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d92314 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8777 q = 1) (hb : d92314 q = 1) : d93630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21522 q ha hb
    | true =>
      simp only [d8777, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8778 q = 1) (hb : d92314 q = 1) : d93631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8779 q = 1) (hb : d92314 q = 1) : d93632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8779, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8793 q = 1) (hb : d92314 q = 1) : d93641 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21523 q ha hb
    | true =>
      simp only [d8793, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21519 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94345 q = 1) : d93642 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94345, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8810 q = 1) (hb : d92314 q = 1) : d8810 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94346 q = 1) : d93643 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94346, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94347 q = 1) : d93644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94347, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94348 q = 1) : d93645 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94348, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1327 q = 1) (hb : d92314 q = 1) : d1327 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d8816 q = 1) (hb : d92314 q = 1) : d93648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8816, d93648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21525 q ha hb
    | true =>
      simp only [d8816, d93648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8817 q = 1) (hb : d92314 q = 1) : d93649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8817, d93649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8817, d93649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8818 q = 1) (hb : d92314 q = 1) : d93650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8818, d93650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d8818, d93650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d8819 q = 1) (hb : d92314 q = 1) : d93651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8819, d93651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8819, d93651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1333 q = 1) (hb : d92314 q = 1) : d1333 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d8821 q = 1) (hb : d92314 q = 1) : d93653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8821, d93653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21526 q ha hb
    | true =>
      simp only [d8821, d93653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d8822 q = 1) (hb : d92314 q = 1) : d93654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8822, d93654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8822, d93654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8823 q = 1) (hb : d92314 q = 1) : d93655 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8823, d93655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d8823, d93655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8826 q = 1) (hb : d92314 q = 1) : d93658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21527 q ha hb
    | true =>
      simp only [d8826, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21528 q ha hb
  have h26 (q : Pattern) (ha : d92314 q = 1) (hb : d94350 q = 1) : d93659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94350, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d8832 q = 1) (hb : d92314 q = 1) : d8832 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d92314 q = 1) (hb : d94351 q = 1) : d93660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d94351, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92314 q = 1) (hb : d94352 q = 1) : d93661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94352, d93661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d94352, d93661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92314 q = 1) (hb : d94353 q = 1) : d93662 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94353, d93662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d94353, d93662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92314 q = 1) (hb : d94354 q = 1) : d93663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94354, d93663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94354, d93663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21530 (p : Pattern) (ha : d92314 p = 1) (hb : d94361 p = 1) : d93677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8826 q = 1) (hb : d92314 q = 1) : d93658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21527 q ha hb
    | true =>
      simp only [d8826, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21528 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94350 q = 1) : d93659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94350, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8832 q = 1) (hb : d92314 q = 1) : d8832 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94351 q = 1) : d93660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94351, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94359 q = 1) : d93675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94359, d93675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94359, d93675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94360 q = 1) : d93676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94360, d93676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94360, d93676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94361 q = 1) : d93677 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94361, d93677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94361, d93677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21531 (p : Pattern) (ha : d8864 p = 1) (hb : d92314 p = 1) : d93686 p = 1 := by
  have h0 (q : Pattern) (ha : d8860 q = 1) (hb : d92313 q = 1) : d8860 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7004 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8861 q = 1) (hb : d92314 q = 1) : d93683 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8861, d92314, d93683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8861, d92314, d93683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8862 q = 1) (hb : d92314 q = 1) : d93684 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8862, d93684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8862, d93684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8863 q = 1) (hb : d92314 q = 1) : d93685 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8863, d93685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8863, d93685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8864 q = 1) (hb : d92314 q = 1) : d93686 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8864, d93686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8864, d93686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21532 (p : Pattern) (ha : d8868 p = 1) (hb : d92314 p = 1) : d93690 p = 1 := by
  have h0 (q : Pattern) (ha : d7004 q = 1) (hb : d92313 q = 1) : d7004 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8865 q = 1) (hb : d92314 q = 1) : d93687 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8865, d92314, d93687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8865, d92314, d93687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8866 q = 1) (hb : d92314 q = 1) : d93688 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8866, d93688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8866, d93688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8867 q = 1) (hb : d92314 q = 1) : d93689 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8867, d93689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8867, d93689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8868 q = 1) (hb : d92314 q = 1) : d93690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8868, d93690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8868, d93690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21533 (p : Pattern) (ha : d92314 p = 1) (hb : d94371 p = 1) : d93696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8869 q = 1) (hb : d92314 q = 1) : d93691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8869, d93691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21531 q ha hb
    | true =>
      simp only [d8869, d93691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21532 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94367 q = 1) : d93692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94367, d93692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94367, d93692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8890 q = 1) (hb : d92314 q = 1) : d8890 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94368 q = 1) : d93693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94368, d93693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94368, d93693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94369 q = 1) : d93694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94369, d93694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94369, d93694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94370 q = 1) : d93695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94370, d93695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94370, d93695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94371 q = 1) : d93696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94371, d93696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94371, d93696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21534 (p : Pattern) (ha : d92314 p = 1) (hb : d94377 p = 1) : d93702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8756 q = 1) (hb : d92314 q = 1) : d93610 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8756, d93610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8756, d93610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21516 q ha hb
  have h2 (q : Pattern) (ha : d8757 q = 1) (hb : d92314 q = 1) : d93611 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8757, d93611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8757, d93611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8765 q = 1) (hb : d92314 q = 1) : d93618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21516 q ha hb
    | true =>
      simp only [d8765, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21518 q ha hb
  have h4 (q : Pattern) (ha : d8766 q = 1) (hb : d92314 q = 1) : d93619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8766, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8767 q = 1) (hb : d92314 q = 1) : d93620 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8767, d93620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8767, d93620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94355 q = 1) : d93664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94355, d93664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21524 q ha hb
    | true =>
      simp only [d94355, d93664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21529 q ha hb
  have h7 (q : Pattern) (ha : d1361 q = 1) (hb : d92314 q = 1) : d1361 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8844 q = 1) (hb : d92314 q = 1) : d93671 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8844, d93671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21520 q ha hb
    | true =>
      simp only [d8844, d93671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94356 q = 1) : d93672 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94356, d93672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94356, d93672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94357 q = 1) : d93673 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94357, d93673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94357, d93673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94358 q = 1) : d93674 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94358, d93674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94358, d93674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94362 q = 1) : d93678 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94362, d93678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94362, d93678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21530 q ha hb
  have h13 (q : Pattern) (ha : d1371 q = 1) (hb : d92314 q = 1) : d1371 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94363 q = 1) : d93679 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94363, d93679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94363, d93679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94364 q = 1) : d93680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94364, d93680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94364, d93680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94365 q = 1) : d93681 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94365, d93681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94365, d93681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92314 q = 1) (hb : d94366 q = 1) : d93682 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94366, d93682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94366, d93682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92314 q = 1) (hb : d94372 q = 1) : d93697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94372, d93697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94372, d93697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21533 q ha hb
  have h19 (q : Pattern) (ha : d1504 q = 1) (hb : d92314 q = 1) : d1504 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92314 q = 1) (hb : d94373 q = 1) : d93698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94373, d93698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94373, d93698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92314 q = 1) (hb : d94374 q = 1) : d93699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94374, d93699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94374, d93699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92314 q = 1) (hb : d94375 q = 1) : d93700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94375, d93700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94375, d93700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92314 q = 1) (hb : d94376 q = 1) : d93701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94376, d93701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94376, d93701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92314 q = 1) (hb : d94377 q = 1) : d93702 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94377, d93702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94377, d93702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro21535 (p : Pattern) (ha : d92314 p = 1) (hb : d94383 p = 1) : d93708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94378 q = 1) : d93703 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94378, d93703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94378, d93703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21534 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94379 q = 1) : d93704 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94379, d93704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94379, d93704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94380 q = 1) : d93705 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94380, d93705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94380, d93705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94381 q = 1) : d93706 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94381, d93706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94381, d93706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94382 q = 1) : d93707 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94382, d93707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94382, d93707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94383 q = 1) : d93708 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94383, d93708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94383, d93708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21536 (p : Pattern) (ha : d8917 p = 1) (hb : d92314 p = 1) : d8976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8913 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8914 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8915 q = 1) (hb : d92314 q = 1) : d8974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8915, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8916 q = 1) (hb : d92314 q = 1) : d8975 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8916, d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8917 q = 1) (hb : d92314 q = 1) : d8976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8917, d8976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8917, d8976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21537 (p : Pattern) (ha : d8923 p = 1) (hb : d92314 p = 1) : d93717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92314 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8918 q = 1) (hb : d92314 q = 1) : d93712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21536 q ha hb
    | true =>
      simp only [d8918, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8919 q = 1) (hb : d92314 q = 1) : d93713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8920 q = 1) (hb : d92314 q = 1) : d93714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8920, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8921 q = 1) (hb : d92314 q = 1) : d93715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8922 q = 1) (hb : d92314 q = 1) : d93716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8923 q = 1) (hb : d92314 q = 1) : d93717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8923, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8923, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21538 (p : Pattern) (ha : d8926 p = 1) (hb : d92314 p = 1) : d8998 p = 1 := by
  have h0 (q : Pattern) (ha : d8913 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8914 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8915 q = 1) (hb : d92314 q = 1) : d8974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8915, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8916 q = 1) (hb : d92314 q = 1) : d8975 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8916, d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8926 q = 1) (hb : d92314 q = 1) : d8998 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8926, d8998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8926, d8998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21539 (p : Pattern) (ha : d8932 p = 1) (hb : d92314 p = 1) : d93725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92314 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8918 q = 1) (hb : d92314 q = 1) : d93712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21536 q ha hb
    | true =>
      simp only [d8918, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8919 q = 1) (hb : d92314 q = 1) : d93713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8920 q = 1) (hb : d92314 q = 1) : d93714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8920, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8921 q = 1) (hb : d92314 q = 1) : d93715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8922 q = 1) (hb : d92314 q = 1) : d93716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d92314 q = 1) : d1633 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8927 q = 1) (hb : d92314 q = 1) : d93720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21538 q ha hb
    | true =>
      simp only [d8927, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8928 q = 1) (hb : d92314 q = 1) : d93721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8929 q = 1) (hb : d92314 q = 1) : d93722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8929, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8930 q = 1) (hb : d92314 q = 1) : d93723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8931 q = 1) (hb : d92314 q = 1) : d93724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8932 q = 1) (hb : d92314 q = 1) : d93725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8932, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8932, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21540 (p : Pattern) (ha : d8960 p = 1) (hb : d92314 p = 1) : d93748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7038 q = 1) (hb : d92313 q = 1) : d7038 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8957 q = 1) (hb : d92314 q = 1) : d93745 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d92314, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8957, d92314, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8958 q = 1) (hb : d92314 q = 1) : d93746 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8958, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8959 q = 1) (hb : d92314 q = 1) : d93747 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8959, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8960 q = 1) (hb : d92314 q = 1) : d93748 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8960, d93748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8960, d93748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21541 (p : Pattern) (ha : d9011 p = 1) (hb : d92314 p = 1) : d93778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92314 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9006 q = 1) (hb : d92314 q = 1) : d93773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9006, d93773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21540 q ha hb
    | true =>
      simp only [d9006, d93773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9007 q = 1) (hb : d92314 q = 1) : d93774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9007, d93774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9007, d93774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9008 q = 1) (hb : d92314 q = 1) : d93775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9008, d93775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9008, d93775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9009 q = 1) (hb : d92314 q = 1) : d93776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9009, d93776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9009, d93776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9010 q = 1) (hb : d92314 q = 1) : d93777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9010, d93777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9010, d93777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1831 q = 1) (hb : d92314 q = 1) : d1831 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9011 q = 1) (hb : d92314 q = 1) : d93778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9011, d93778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9011, d93778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21542 (p : Pattern) (ha : d8937 p = 1) (hb : d92314 p = 1) : d93730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8913 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8914 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8915 q = 1) (hb : d92314 q = 1) : d8974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8915, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8936 q = 1) (hb : d92314 q = 1) : d93729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8937 q = 1) (hb : d92314 q = 1) : d93730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8937, d93730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8937, d93730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21543 (p : Pattern) (ha : d8944 p = 1) (hb : d92314 p = 1) : d93737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8913 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8914 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8942 q = 1) (hb : d92314 q = 1) : d93735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8943 q = 1) (hb : d92314 q = 1) : d93736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8943, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8944 q = 1) (hb : d92314 q = 1) : d93737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8944, d93737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8944, d93737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21544 (p : Pattern) (ha : d8956 p = 1) (hb : d92314 p = 1) : d93744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8952 q = 1) (hb : d92313 q = 1) : d8952 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7038 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8953 q = 1) (hb : d92314 q = 1) : d93741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d92314, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8953, d92314, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8954 q = 1) (hb : d92314 q = 1) : d93742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8954, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8955 q = 1) (hb : d92314 q = 1) : d93743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8955, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8956 q = 1) (hb : d92314 q = 1) : d93744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8956, d93744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8956, d93744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21545 (p : Pattern) (ha : d92314 p = 1) (hb : d94391 p = 1) : d93754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d92314 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8938 q = 1) (hb : d92314 q = 1) : d93731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21542 q ha hb
    | true =>
      simp only [d8938, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8939 q = 1) (hb : d92314 q = 1) : d93732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8940 q = 1) (hb : d92314 q = 1) : d93733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8940, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8941 q = 1) (hb : d92314 q = 1) : d93734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d92314 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8945 q = 1) (hb : d92314 q = 1) : d93738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21543 q ha hb
    | true =>
      simp only [d8945, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8946 q = 1) (hb : d92314 q = 1) : d93739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8947 q = 1) (hb : d92314 q = 1) : d93740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8947, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8961 q = 1) (hb : d92314 q = 1) : d93749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21544 q ha hb
    | true =>
      simp only [d8961, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21540 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94387 q = 1) : d93750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94387, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8978 q = 1) (hb : d92314 q = 1) : d8978 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94388 q = 1) : d93751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94388, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94389 q = 1) : d93752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94389, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94390 q = 1) : d93753 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94390, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94391 q = 1) : d93754 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94391, d93754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94391, d93754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21546 (p : Pattern) (ha : d8983 p = 1) (hb : d92314 p = 1) : d93755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8913 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8914 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8915 q = 1) (hb : d92314 q = 1) : d8974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8915, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8936 q = 1) (hb : d92314 q = 1) : d93729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8983 q = 1) (hb : d92314 q = 1) : d93755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8983, d93755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8983, d93755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21547 (p : Pattern) (ha : d8988 p = 1) (hb : d92314 p = 1) : d93760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8913 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8914 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8914, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8942 q = 1) (hb : d92314 q = 1) : d93735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8943 q = 1) (hb : d92314 q = 1) : d93736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8943, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8988 q = 1) (hb : d92314 q = 1) : d93760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8988, d93760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8988, d93760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21548 (p : Pattern) (ha : d8992 p = 1) (hb : d92314 p = 1) : d93764 p = 1 := by
  have h0 (q : Pattern) (ha : d8952 q = 1) (hb : d92313 q = 1) : d8952 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8953 q = 1) (hb : d92314 q = 1) : d93741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d92314, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8953, d92314, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8954 q = 1) (hb : d92314 q = 1) : d93742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8954, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8955 q = 1) (hb : d92314 q = 1) : d93743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8955, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8992 q = 1) (hb : d92314 q = 1) : d93764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8992, d93764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8992, d93764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21549 (p : Pattern) (ha : d8993 p = 1) (hb : d92314 p = 1) : d93765 p = 1 := by
  have h0 (q : Pattern) (ha : d7038 q = 1) (hb : d92313 q = 1) : d7038 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8957 q = 1) (hb : d92314 q = 1) : d93745 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d92314, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8957, d92314, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8958 q = 1) (hb : d92314 q = 1) : d93746 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8958, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8959 q = 1) (hb : d92314 q = 1) : d93747 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8959, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8993 q = 1) (hb : d92314 q = 1) : d93765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8993, d93765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8993, d93765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21550 (p : Pattern) (ha : d92314 p = 1) (hb : d94396 p = 1) : d93771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d92314 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8938 q = 1) (hb : d92314 q = 1) : d93731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21542 q ha hb
    | true =>
      simp only [d8938, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8939 q = 1) (hb : d92314 q = 1) : d93732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8940 q = 1) (hb : d92314 q = 1) : d93733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8940, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8941 q = 1) (hb : d92314 q = 1) : d93734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d92314 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8945 q = 1) (hb : d92314 q = 1) : d93738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21543 q ha hb
    | true =>
      simp only [d8945, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8946 q = 1) (hb : d92314 q = 1) : d93739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8947 q = 1) (hb : d92314 q = 1) : d93740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8947, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8961 q = 1) (hb : d92314 q = 1) : d93749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21544 q ha hb
    | true =>
      simp only [d8961, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21540 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94387 q = 1) : d93750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94387, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8978 q = 1) (hb : d92314 q = 1) : d8978 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94388 q = 1) : d93751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94388, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94389 q = 1) : d93752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94389, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94390 q = 1) : d93753 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94390, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1804 q = 1) (hb : d92314 q = 1) : d1804 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d8984 q = 1) (hb : d92314 q = 1) : d93756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8984, d93756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21546 q ha hb
    | true =>
      simp only [d8984, d93756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8985 q = 1) (hb : d92314 q = 1) : d93757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8985, d93757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8985, d93757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8986 q = 1) (hb : d92314 q = 1) : d93758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8986, d93758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d8986, d93758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d8987 q = 1) (hb : d92314 q = 1) : d93759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8987, d93759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8987, d93759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1810 q = 1) (hb : d92314 q = 1) : d1810 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d8989 q = 1) (hb : d92314 q = 1) : d93761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8989, d93761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21547 q ha hb
    | true =>
      simp only [d8989, d93761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d8990 q = 1) (hb : d92314 q = 1) : d93762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8990, d93762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8990, d93762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8991 q = 1) (hb : d92314 q = 1) : d93763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8991, d93763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d8991, d93763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8994 q = 1) (hb : d92314 q = 1) : d93766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21548 q ha hb
    | true =>
      simp only [d8994, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21549 q ha hb
  have h26 (q : Pattern) (ha : d92314 q = 1) (hb : d94392 q = 1) : d93767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94392, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d9000 q = 1) (hb : d92314 q = 1) : d9000 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d92314 q = 1) (hb : d94393 q = 1) : d93768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d94393, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92314 q = 1) (hb : d94394 q = 1) : d93769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94394, d93769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d94394, d93769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92314 q = 1) (hb : d94395 q = 1) : d93770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94395, d93770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d94395, d93770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92314 q = 1) (hb : d94396 q = 1) : d93771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94396, d93771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94396, d93771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21551 (p : Pattern) (ha : d92314 p = 1) (hb : d94403 p = 1) : d93785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8994 q = 1) (hb : d92314 q = 1) : d93766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21548 q ha hb
    | true =>
      simp only [d8994, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21549 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94392 q = 1) : d93767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94392, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9000 q = 1) (hb : d92314 q = 1) : d9000 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94393 q = 1) : d93768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94393, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94401 q = 1) : d93783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94401, d93783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94401, d93783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94402 q = 1) : d93784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94402, d93784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94402, d93784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94403 q = 1) : d93785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94403, d93785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94403, d93785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21552 (p : Pattern) (ha : d9032 p = 1) (hb : d92314 p = 1) : d93794 p = 1 := by
  have h0 (q : Pattern) (ha : d9028 q = 1) (hb : d92313 q = 1) : d9028 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7084 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9029 q = 1) (hb : d92314 q = 1) : d93791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9029, d92314, d93791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9029, d92314, d93791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9030 q = 1) (hb : d92314 q = 1) : d93792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9030, d93792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9030, d93792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9031 q = 1) (hb : d92314 q = 1) : d93793 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9031, d93793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9031, d93793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9032 q = 1) (hb : d92314 q = 1) : d93794 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9032, d93794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9032, d93794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21553 (p : Pattern) (ha : d9036 p = 1) (hb : d92314 p = 1) : d93798 p = 1 := by
  have h0 (q : Pattern) (ha : d7084 q = 1) (hb : d92313 q = 1) : d7084 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9033 q = 1) (hb : d92314 q = 1) : d93795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9033, d92314, d93795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9033, d92314, d93795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9034 q = 1) (hb : d92314 q = 1) : d93796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9034, d93796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9034, d93796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9035 q = 1) (hb : d92314 q = 1) : d93797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9035, d93797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9035, d93797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9036 q = 1) (hb : d92314 q = 1) : d93798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9036, d93798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9036, d93798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21554 (p : Pattern) (ha : d92314 p = 1) (hb : d94413 p = 1) : d93804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9037 q = 1) (hb : d92314 q = 1) : d93799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9037, d93799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21552 q ha hb
    | true =>
      simp only [d9037, d93799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21553 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94409 q = 1) : d93800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94409, d93800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94409, d93800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9058 q = 1) (hb : d92314 q = 1) : d9058 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94410 q = 1) : d93801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94410, d93801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94410, d93801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94411 q = 1) : d93802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94411, d93802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94411, d93802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94412 q = 1) : d93803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94412, d93803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94412, d93803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94413 q = 1) : d93804 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94413, d93804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94413, d93804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21555 (p : Pattern) (ha : d92314 p = 1) (hb : d94419 p = 1) : d93810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8924 q = 1) (hb : d92314 q = 1) : d93718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8924, d93718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8924, d93718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21537 q ha hb
  have h2 (q : Pattern) (ha : d8925 q = 1) (hb : d92314 q = 1) : d93719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8925, d93719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8925, d93719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8933 q = 1) (hb : d92314 q = 1) : d93726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21537 q ha hb
    | true =>
      simp only [d8933, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21539 q ha hb
  have h4 (q : Pattern) (ha : d8934 q = 1) (hb : d92314 q = 1) : d93727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8934, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8935 q = 1) (hb : d92314 q = 1) : d93728 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8935, d93728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8935, d93728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94397 q = 1) : d93772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94397, d93772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21545 q ha hb
    | true =>
      simp only [d94397, d93772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21550 q ha hb
  have h7 (q : Pattern) (ha : d1838 q = 1) (hb : d92314 q = 1) : d1838 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9012 q = 1) (hb : d92314 q = 1) : d93779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9012, d93779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21541 q ha hb
    | true =>
      simp only [d9012, d93779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94398 q = 1) : d93780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94398, d93780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94398, d93780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94399 q = 1) : d93781 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94399, d93781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94399, d93781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94400 q = 1) : d93782 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94400, d93782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94400, d93782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94404 q = 1) : d93786 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94404, d93786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94404, d93786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21551 q ha hb
  have h13 (q : Pattern) (ha : d1848 q = 1) (hb : d92314 q = 1) : d1848 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94405 q = 1) : d93787 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94405, d93787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94405, d93787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94406 q = 1) : d93788 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94406, d93788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94406, d93788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94407 q = 1) : d93789 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94407, d93789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94407, d93789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92314 q = 1) (hb : d94408 q = 1) : d93790 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94408, d93790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94408, d93790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92314 q = 1) (hb : d94414 q = 1) : d93805 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94414, d93805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94414, d93805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21554 q ha hb
  have h19 (q : Pattern) (ha : d1981 q = 1) (hb : d92314 q = 1) : d1981 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92314 q = 1) (hb : d94415 q = 1) : d93806 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94415, d93806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94415, d93806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92314 q = 1) (hb : d94416 q = 1) : d93807 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94416, d93807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94416, d93807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92314 q = 1) (hb : d94417 q = 1) : d93808 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94417, d93808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94417, d93808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92314 q = 1) (hb : d94418 q = 1) : d93809 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94418, d93809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94418, d93809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92314 q = 1) (hb : d94419 q = 1) : d93810 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94419, d93810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94419, d93810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro21556 (p : Pattern) (ha : d92314 p = 1) (hb : d94425 p = 1) : d93816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94420 q = 1) : d93811 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94420, d93811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94420, d93811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21555 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94421 q = 1) : d93812 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94421, d93812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94421, d93812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94422 q = 1) : d93813 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94422, d93813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94422, d93813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94423 q = 1) : d93814 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94423, d93814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94423, d93814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94424 q = 1) : d93815 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94424, d93815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94424, d93815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94425 q = 1) : d93816 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94425, d93816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94425, d93816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21557 (p : Pattern) (ha : d9086 p = 1) (hb : d92314 p = 1) : d9145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9082 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9083 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9084 q = 1) (hb : d92314 q = 1) : d9143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9084, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9085 q = 1) (hb : d92314 q = 1) : d9144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9085, d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9086 q = 1) (hb : d92314 q = 1) : d9145 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9086, d9145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9086, d9145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21558 (p : Pattern) (ha : d9092 p = 1) (hb : d92314 p = 1) : d93826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92314 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9087 q = 1) (hb : d92314 q = 1) : d93821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21557 q ha hb
    | true =>
      simp only [d9087, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9088 q = 1) (hb : d92314 q = 1) : d93822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9089 q = 1) (hb : d92314 q = 1) : d93823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9089, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9090 q = 1) (hb : d92314 q = 1) : d93824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9091 q = 1) (hb : d92314 q = 1) : d93825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9092 q = 1) (hb : d92314 q = 1) : d93826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9092, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9092, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21559 (p : Pattern) (ha : d9095 p = 1) (hb : d92314 p = 1) : d9167 p = 1 := by
  have h0 (q : Pattern) (ha : d9082 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9083 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9084 q = 1) (hb : d92314 q = 1) : d9143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9084, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9085 q = 1) (hb : d92314 q = 1) : d9144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9085, d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9095 q = 1) (hb : d92314 q = 1) : d9167 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9095, d9167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9095, d9167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21560 (p : Pattern) (ha : d9101 p = 1) (hb : d92314 p = 1) : d93834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92314 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9087 q = 1) (hb : d92314 q = 1) : d93821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21557 q ha hb
    | true =>
      simp only [d9087, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9088 q = 1) (hb : d92314 q = 1) : d93822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9089 q = 1) (hb : d92314 q = 1) : d93823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9089, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9090 q = 1) (hb : d92314 q = 1) : d93824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9091 q = 1) (hb : d92314 q = 1) : d93825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d92314 q = 1) : d2116 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9096 q = 1) (hb : d92314 q = 1) : d93829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21559 q ha hb
    | true =>
      simp only [d9096, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9097 q = 1) (hb : d92314 q = 1) : d93830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9098 q = 1) (hb : d92314 q = 1) : d93831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9098, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9099 q = 1) (hb : d92314 q = 1) : d93832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9100 q = 1) (hb : d92314 q = 1) : d93833 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9101 q = 1) (hb : d92314 q = 1) : d93834 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9101, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9101, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21561 (p : Pattern) (ha : d9129 p = 1) (hb : d92314 p = 1) : d93857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7119 q = 1) (hb : d92313 q = 1) : d7119 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9126 q = 1) (hb : d92314 q = 1) : d93854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, d92314, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9126, d92314, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9127 q = 1) (hb : d92314 q = 1) : d93855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9127, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9128 q = 1) (hb : d92314 q = 1) : d93856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9128, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9129 q = 1) (hb : d92314 q = 1) : d93857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9129, d93857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9129, d93857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21562 (p : Pattern) (ha : d9180 p = 1) (hb : d92314 p = 1) : d93887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92314 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9175 q = 1) (hb : d92314 q = 1) : d93882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9175, d93882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21561 q ha hb
    | true =>
      simp only [d9175, d93882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9176 q = 1) (hb : d92314 q = 1) : d93883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9176, d93883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9176, d93883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9177 q = 1) (hb : d92314 q = 1) : d93884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9177, d93884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9177, d93884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9178 q = 1) (hb : d92314 q = 1) : d93885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9178, d93885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9178, d93885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9179 q = 1) (hb : d92314 q = 1) : d93886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9179, d93886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9179, d93886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2309 q = 1) (hb : d92314 q = 1) : d2309 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9180 q = 1) (hb : d92314 q = 1) : d93887 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9180, d93887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9180, d93887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21563 (p : Pattern) (ha : d9106 p = 1) (hb : d92314 p = 1) : d93839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9082 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9083 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9084 q = 1) (hb : d92314 q = 1) : d9143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9084, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9105 q = 1) (hb : d92314 q = 1) : d93838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9106 q = 1) (hb : d92314 q = 1) : d93839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9106, d93839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9106, d93839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21564 (p : Pattern) (ha : d9113 p = 1) (hb : d92314 p = 1) : d93846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9082 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9083 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9111 q = 1) (hb : d92314 q = 1) : d93844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9112 q = 1) (hb : d92314 q = 1) : d93845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9112, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9113 q = 1) (hb : d92314 q = 1) : d93846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9113, d93846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9113, d93846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21565 (p : Pattern) (ha : d9125 p = 1) (hb : d92314 p = 1) : d93853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9121 q = 1) (hb : d92313 q = 1) : d9121 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7119 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9122 q = 1) (hb : d92314 q = 1) : d93850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, d92314, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9122, d92314, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9123 q = 1) (hb : d92314 q = 1) : d93851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9123, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9124 q = 1) (hb : d92314 q = 1) : d93852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9124, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9125 q = 1) (hb : d92314 q = 1) : d93853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9125, d93853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9125, d93853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21566 (p : Pattern) (ha : d92314 p = 1) (hb : d94434 p = 1) : d93863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d92314 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9107 q = 1) (hb : d92314 q = 1) : d93840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21563 q ha hb
    | true =>
      simp only [d9107, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9108 q = 1) (hb : d92314 q = 1) : d93841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9109 q = 1) (hb : d92314 q = 1) : d93842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9109, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9110 q = 1) (hb : d92314 q = 1) : d93843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d92314 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9114 q = 1) (hb : d92314 q = 1) : d93847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21564 q ha hb
    | true =>
      simp only [d9114, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9115 q = 1) (hb : d92314 q = 1) : d93848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9116 q = 1) (hb : d92314 q = 1) : d93849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9116, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9130 q = 1) (hb : d92314 q = 1) : d93858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21565 q ha hb
    | true =>
      simp only [d9130, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21561 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94430 q = 1) : d93859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94430, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d9147 q = 1) (hb : d92314 q = 1) : d9147 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94431 q = 1) : d93860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94431, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94432 q = 1) : d93861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94432, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94433 q = 1) : d93862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94433, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94434 q = 1) : d93863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94434, d93863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94434, d93863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21567 (p : Pattern) (ha : d9152 p = 1) (hb : d92314 p = 1) : d93864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9082 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9083 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9084 q = 1) (hb : d92314 q = 1) : d9143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9084, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9105 q = 1) (hb : d92314 q = 1) : d93838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9152 q = 1) (hb : d92314 q = 1) : d93864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9152, d93864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9152, d93864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21568 (p : Pattern) (ha : d9157 p = 1) (hb : d92314 p = 1) : d93869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9082 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9083 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9083, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9111 q = 1) (hb : d92314 q = 1) : d93844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9112 q = 1) (hb : d92314 q = 1) : d93845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9112, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9157 q = 1) (hb : d92314 q = 1) : d93869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9157, d93869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9157, d93869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21569 (p : Pattern) (ha : d9161 p = 1) (hb : d92314 p = 1) : d93873 p = 1 := by
  have h0 (q : Pattern) (ha : d9121 q = 1) (hb : d92313 q = 1) : d9121 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9122 q = 1) (hb : d92314 q = 1) : d93850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, d92314, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9122, d92314, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9123 q = 1) (hb : d92314 q = 1) : d93851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9123, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9124 q = 1) (hb : d92314 q = 1) : d93852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9124, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9161 q = 1) (hb : d92314 q = 1) : d93873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9161, d93873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9161, d93873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21570 (p : Pattern) (ha : d9162 p = 1) (hb : d92314 p = 1) : d93874 p = 1 := by
  have h0 (q : Pattern) (ha : d7119 q = 1) (hb : d92313 q = 1) : d7119 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9126 q = 1) (hb : d92314 q = 1) : d93854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, d92314, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9126, d92314, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9127 q = 1) (hb : d92314 q = 1) : d93855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9127, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9128 q = 1) (hb : d92314 q = 1) : d93856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9128, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9162 q = 1) (hb : d92314 q = 1) : d93874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9162, d93874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9162, d93874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21571 (p : Pattern) (ha : d92314 p = 1) (hb : d94439 p = 1) : d93880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d92314 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9107 q = 1) (hb : d92314 q = 1) : d93840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21563 q ha hb
    | true =>
      simp only [d9107, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9108 q = 1) (hb : d92314 q = 1) : d93841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9109 q = 1) (hb : d92314 q = 1) : d93842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9109, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9110 q = 1) (hb : d92314 q = 1) : d93843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d92314 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9114 q = 1) (hb : d92314 q = 1) : d93847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21564 q ha hb
    | true =>
      simp only [d9114, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9115 q = 1) (hb : d92314 q = 1) : d93848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9116 q = 1) (hb : d92314 q = 1) : d93849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9116, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9130 q = 1) (hb : d92314 q = 1) : d93858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21565 q ha hb
    | true =>
      simp only [d9130, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21561 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94430 q = 1) : d93859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94430, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d9147 q = 1) (hb : d92314 q = 1) : d9147 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94431 q = 1) : d93860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94431, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94432 q = 1) : d93861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94432, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94433 q = 1) : d93862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94433, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2282 q = 1) (hb : d92314 q = 1) : d2282 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d9153 q = 1) (hb : d92314 q = 1) : d93865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9153, d93865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21567 q ha hb
    | true =>
      simp only [d9153, d93865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9154 q = 1) (hb : d92314 q = 1) : d93866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9154, d93866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9154, d93866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9155 q = 1) (hb : d92314 q = 1) : d93867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9155, d93867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9155, d93867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d9156 q = 1) (hb : d92314 q = 1) : d93868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9156, d93868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9156, d93868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d2288 q = 1) (hb : d92314 q = 1) : d2288 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d9158 q = 1) (hb : d92314 q = 1) : d93870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9158, d93870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21568 q ha hb
    | true =>
      simp only [d9158, d93870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9159 q = 1) (hb : d92314 q = 1) : d93871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9159, d93871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9159, d93871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9160 q = 1) (hb : d92314 q = 1) : d93872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9160, d93872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d9160, d93872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9163 q = 1) (hb : d92314 q = 1) : d93875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21569 q ha hb
    | true =>
      simp only [d9163, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21570 q ha hb
  have h26 (q : Pattern) (ha : d92314 q = 1) (hb : d94435 q = 1) : d93876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94435, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d9169 q = 1) (hb : d92314 q = 1) : d9169 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d92314 q = 1) (hb : d94436 q = 1) : d93877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d94436, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92314 q = 1) (hb : d94437 q = 1) : d93878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94437, d93878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d94437, d93878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92314 q = 1) (hb : d94438 q = 1) : d93879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94438, d93879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d94438, d93879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92314 q = 1) (hb : d94439 q = 1) : d93880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94439, d93880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94439, d93880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21572 (p : Pattern) (ha : d92314 p = 1) (hb : d94446 p = 1) : d93894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9163 q = 1) (hb : d92314 q = 1) : d93875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21569 q ha hb
    | true =>
      simp only [d9163, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21570 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94435 q = 1) : d93876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94435, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9169 q = 1) (hb : d92314 q = 1) : d9169 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94436 q = 1) : d93877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94436, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94444 q = 1) : d93892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94444, d93892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94444, d93892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94445 q = 1) : d93893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94445, d93893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94445, d93893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94446 q = 1) : d93894 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94446, d93894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94446, d93894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21573 (p : Pattern) (ha : d9201 p = 1) (hb : d92314 p = 1) : d93903 p = 1 := by
  have h0 (q : Pattern) (ha : d9197 q = 1) (hb : d92313 q = 1) : d9197 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9198 q = 1) (hb : d92314 q = 1) : d93900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9198, d92314, d93900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9198, d92314, d93900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9199 q = 1) (hb : d92314 q = 1) : d93901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9199, d93901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9199, d93901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9200 q = 1) (hb : d92314 q = 1) : d93902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9200, d93902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9200, d93902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9201 q = 1) (hb : d92314 q = 1) : d93903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9201, d93903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9201, d93903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21574 (p : Pattern) (ha : d9205 p = 1) (hb : d92314 p = 1) : d93907 p = 1 := by
  have h0 (q : Pattern) (ha : d7165 q = 1) (hb : d92313 q = 1) : d7165 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2387 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9202 q = 1) (hb : d92314 q = 1) : d93904 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9202, d92314, d93904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9202, d92314, d93904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9203 q = 1) (hb : d92314 q = 1) : d93905 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9203, d93905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9203, d93905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9204 q = 1) (hb : d92314 q = 1) : d93906 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9204, d93906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9204, d93906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9205 q = 1) (hb : d92314 q = 1) : d93907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9205, d93907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9205, d93907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro21575 (p : Pattern) (ha : d92314 p = 1) (hb : d94456 p = 1) : d93913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9206 q = 1) (hb : d92314 q = 1) : d93908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9206, d93908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21573 q ha hb
    | true =>
      simp only [d9206, d93908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21574 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94452 q = 1) : d93909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94452, d93909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94452, d93909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9227 q = 1) (hb : d92314 q = 1) : d9227 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94453 q = 1) : d93910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94453, d93910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94453, d93910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94454 q = 1) : d93911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94454, d93911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94454, d93911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94455 q = 1) : d93912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94455, d93912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94455, d93912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94456 q = 1) : d93913 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94456, d93913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94456, d93913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21576 (p : Pattern) (ha : d92314 p = 1) (hb : d94462 p = 1) : d93919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9093 q = 1) (hb : d92314 q = 1) : d93827 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9093, d93827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9093, d93827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21558 q ha hb
  have h2 (q : Pattern) (ha : d9094 q = 1) (hb : d92314 q = 1) : d93828 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9094, d93828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9094, d93828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9102 q = 1) (hb : d92314 q = 1) : d93835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21558 q ha hb
    | true =>
      simp only [d9102, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21560 q ha hb
  have h4 (q : Pattern) (ha : d9103 q = 1) (hb : d92314 q = 1) : d93836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9103, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9104 q = 1) (hb : d92314 q = 1) : d93837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9104, d93837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9104, d93837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94440 q = 1) : d93881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94440, d93881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21566 q ha hb
    | true =>
      simp only [d94440, d93881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21571 q ha hb
  have h7 (q : Pattern) (ha : d2316 q = 1) (hb : d92314 q = 1) : d2316 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9181 q = 1) (hb : d92314 q = 1) : d93888 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9181, d93888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21562 q ha hb
    | true =>
      simp only [d9181, d93888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94441 q = 1) : d93889 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94441, d93889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94441, d93889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94442 q = 1) : d93890 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94442, d93890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94442, d93890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94443 q = 1) : d93891 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94443, d93891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94443, d93891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94447 q = 1) : d93895 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94447, d93895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94447, d93895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21572 q ha hb
  have h13 (q : Pattern) (ha : d2326 q = 1) (hb : d92314 q = 1) : d2326 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94448 q = 1) : d93896 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94448, d93896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94448, d93896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94449 q = 1) : d93897 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94449, d93897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94449, d93897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94450 q = 1) : d93898 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94450, d93898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94450, d93898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92314 q = 1) (hb : d94451 q = 1) : d93899 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94451, d93899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94451, d93899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92314 q = 1) (hb : d94457 q = 1) : d93914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94457, d93914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94457, d93914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21575 q ha hb
  have h19 (q : Pattern) (ha : d2459 q = 1) (hb : d92314 q = 1) : d2459 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92314 q = 1) (hb : d94458 q = 1) : d93915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94458, d93915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94458, d93915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92314 q = 1) (hb : d94459 q = 1) : d93916 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94459, d93916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94459, d93916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92314 q = 1) (hb : d94460 q = 1) : d93917 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94460, d93917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94460, d93917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92314 q = 1) (hb : d94461 q = 1) : d93918 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94461, d93918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94461, d93918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92314 q = 1) (hb : d94462 q = 1) : d93919 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94462, d93919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94462, d93919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro21577 (p : Pattern) (ha : d92314 p = 1) (hb : d94468 p = 1) : d93925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94463 q = 1) : d93920 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94463, d93920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94463, d93920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21576 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94464 q = 1) : d93921 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94464, d93921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94464, d93921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94465 q = 1) : d93922 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94465, d93922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94465, d93922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94466 q = 1) : d93923 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94466, d93923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94466, d93923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94467 q = 1) : d93924 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94467, d93924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94467, d93924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94468 q = 1) : d93925 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94468, d93925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94468, d93925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21578 (p : Pattern) (ha : d92314 p = 1) (hb : d94474 p = 1) : d93931 p = 1 := by
  have h0 (q : Pattern) (ha : d92314 q = 1) (hb : d94303 q = 1) : d93496 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94303, d93496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21472 q ha hb
    | true =>
      simp only [d94303, d93496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21493 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94343 q = 1) : d93602 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94343, d93602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94343, d93602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21514 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94344 q = 1) : d93603 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94344, d93603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94344, d93603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94384 q = 1) : d93709 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94384, d93709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94384, d93709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21535 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94385 q = 1) : d93710 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94385, d93710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94385, d93710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94386 q = 1) : d93711 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94386, d93711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94386, d93711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94426 q = 1) : d93817 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94426, d93817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94426, d93817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21556 q ha hb
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94427 q = 1) : d93818 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94427, d93818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94427, d93818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94428 q = 1) : d93819 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94428, d93819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94428, d93819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94429 q = 1) : d93820 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94429, d93820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94429, d93820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94469 q = 1) : d93926 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94469, d93926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94469, d93926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21577 q ha hb
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94470 q = 1) : d93927 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94470, d93927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94470, d93927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94471 q = 1) : d93928 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94471, d93928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94471, d93928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94472 q = 1) : d93929 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94472, d93929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94472, d93929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94473 q = 1) : d93930 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94473, d93930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94473, d93930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94474 q = 1) : d93931 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94474, d93931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94474, d93931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro21579 (p : Pattern) (ha : d92314 p = 1) (hb : d94480 p = 1) : d93937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94475 q = 1) : d93932 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94475, d93932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21578 q ha hb
    | true =>
      simp only [d94475, d93932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94476 q = 1) : d93933 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94476, d93933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94476, d93933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94477 q = 1) : d93934 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94477, d93934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94477, d93934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94478 q = 1) : d93935 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94478, d93935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94478, d93935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94479 q = 1) : d93936 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94479, d93936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94479, d93936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94480 q = 1) : d93937 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94480, d93937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94480, d93937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21580 (p : Pattern) (ha : d92314 p = 1) (hb : d94486 p = 1) : d93943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94481 q = 1) : d93938 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94481, d93938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21579 q ha hb
    | true =>
      simp only [d94481, d93938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94482 q = 1) : d93939 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94482, d93939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94482, d93939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94483 q = 1) : d93940 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94483, d93940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94483, d93940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94484 q = 1) : d93941 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94484, d93941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94484, d93941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94485 q = 1) : d93942 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94485, d93942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94485, d93942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94486 q = 1) : d93943 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94486, d93943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94486, d93943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21581 (p : Pattern) (ha : d92314 p = 1) (hb : d94492 p = 1) : d93949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94487 q = 1) : d93944 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94487, d93944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21580 q ha hb
    | true =>
      simp only [d94487, d93944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94488 q = 1) : d93945 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94488, d93945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94488, d93945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94489 q = 1) : d93946 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94489, d93946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94489, d93946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94490 q = 1) : d93947 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94490, d93947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94490, d93947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94491 q = 1) : d93948 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94491, d93948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94491, d93948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94492 q = 1) : d93949 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94492, d93949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94492, d93949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21582 (p : Pattern) (ha : d92314 p = 1) (hb : d94498 p = 1) : d93955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94493 q = 1) : d93950 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94493, d93950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21581 q ha hb
    | true =>
      simp only [d94493, d93950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94494 q = 1) : d93951 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94494, d93951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94494, d93951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94495 q = 1) : d93952 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94495, d93952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94495, d93952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94496 q = 1) : d93953 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94496, d93953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94496, d93953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94497 q = 1) : d93954 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94497, d93954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94497, d93954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94498 q = 1) : d93955 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94498, d93955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94498, d93955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21583 (p : Pattern) (ha : d92317 p = 1) (hb : d94504 p = 1) : d93961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94499 q = 1) : d93956 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94499, d93956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21582 q ha hb
    | true =>
      simp only [d94499, d93956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94500 q = 1) : d93957 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94500, d93957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94500, d93957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92316 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92317 q = 1) (hb : d94501 q = 1) : d93958 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d92317, d94501, d93958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92317, d94501, d93958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92317 q = 1) (hb : d94502 q = 1) : d93959 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94502, d93959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94502, d93959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92317 q = 1) (hb : d94503 q = 1) : d93960 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94503, d93960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94503, d93960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d92317 q = 1) (hb : d94504 q = 1) : d93961 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94504, d93961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94504, d93961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h8 p ha hb
theorem andIntro21584 (p : Pattern) (ha : d92317 p = 1) (hb : d94510 p = 1) : d93967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92317 q = 1) (hb : d94505 q = 1) : d93962 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94505, d93962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21583 q ha hb
    | true =>
      simp only [d94505, d93962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92317 q = 1) (hb : d94506 q = 1) : d93963 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94506, d93963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94506, d93963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92317 q = 1) (hb : d94507 q = 1) : d93964 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94507, d93964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94507, d93964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92317 q = 1) (hb : d94508 q = 1) : d93965 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94508, d93965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94508, d93965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92317 q = 1) (hb : d94509 q = 1) : d93966 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94509, d93966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94509, d93966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92317 q = 1) (hb : d94510 q = 1) : d93967 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94510, d93967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94510, d93967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21585 (p : Pattern) (ha : d92317 p = 1) (hb : d94516 p = 1) : d93973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92317 q = 1) (hb : d94511 q = 1) : d93968 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94511, d93968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21584 q ha hb
    | true =>
      simp only [d94511, d93968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92317 q = 1) (hb : d94512 q = 1) : d93969 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94512, d93969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94512, d93969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92317 q = 1) (hb : d94513 q = 1) : d93970 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94513, d93970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94513, d93970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92317 q = 1) (hb : d94514 q = 1) : d93971 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94514, d93971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94514, d93971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92317 q = 1) (hb : d94515 q = 1) : d93972 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94515, d93972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94515, d93972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92317 q = 1) (hb : d94516 q = 1) : d93973 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94516, d93973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94516, d93973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21586 (p : Pattern) (ha : d75636 p = 1) (hb : d93275 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d75631 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q hb ha
    | true =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75632 q = 1) (hb : d93271 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75632, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75632, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d75633 q = 1) (hb : d93272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75633, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75633, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75634 q = 1) (hb : d93273 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75634, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d75634, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75635 q = 1) (hb : d93274 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75635, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75635, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75636 q = 1) (hb : d93275 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75636, d93275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75636, d93275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21587 (p : Pattern) (ha : d75642 p = 1) (hb : d93281 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d75631 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q hb ha
    | true =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75632 q = 1) (hb : d93271 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75632, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75632, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d75633 q = 1) (hb : d93272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75633, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75633, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75634 q = 1) (hb : d93273 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75634, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d75634, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75635 q = 1) (hb : d93274 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75635, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75635, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d75637 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75637, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18944 q hb ha
    | true =>
      simp only [d75637, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d75638 q = 1) (hb : d93277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75638, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d75638, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d75639 q = 1) (hb : d93278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75639, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d75639, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d75640 q = 1) (hb : d93279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75640, d93279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d75640, d93279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d75641 q = 1) (hb : d93280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75641, d93280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d75641, d93280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d75642 q = 1) (hb : d93281 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75642, d93281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75642, d93281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21588 (p : Pattern) (ha : d75649 p = 1) (hb : d93288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75637 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75637, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18944 q hb ha
    | true =>
      simp only [d75637, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75638 q = 1) (hb : d93277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75638, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75638, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d75639 q = 1) (hb : d93278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75639, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75639, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75647 q = 1) (hb : d93286 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75647, d93286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75647, d93286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75648 q = 1) (hb : d93287 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75648, d93287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75648, d93287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75649 q = 1) (hb : d93288 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75649, d93288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75649, d93288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21589 (p : Pattern) (ha : d75660 p = 1) (hb : d93299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75655 q = 1) (hb : d93294 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75655, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18949 q hb ha
    | true =>
      simp only [d75655, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75656 q = 1) (hb : d93295 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75656, d93295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75656, d93295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d75657 q = 1) (hb : d93296 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75657, d93296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75657, d93296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75658 q = 1) (hb : d93297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75658, d93297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75658, d93297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75659 q = 1) (hb : d93298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75659, d93298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75659, d93298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75660 q = 1) (hb : d93299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75660, d93299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75660, d93299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21590 (p : Pattern) (ha : d75666 p = 1) (hb : d93305 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d75643 q = 1) (hb : d93282 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75643, d93282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21586 q ha hb
    | true =>
      simp only [d75643, d93282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21587 q ha hb
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
  have h8 (q : Pattern) (ha : d75644 q = 1) (hb : d93283 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75644, d93283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75644, d93283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75645 q = 1) (hb : d93284 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75645, d93284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75645, d93284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75646 q = 1) (hb : d93285 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75646, d93285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d75646, d93285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75650 q = 1) (hb : d93289 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75650, d93289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75650, d93289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21588 q ha hb
  have h12 (q : Pattern) (ha : d75651 q = 1) (hb : d93290 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75651, d93290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d75651, d93290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d75652 q = 1) (hb : d93291 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75652, d93291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d75652, d93291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d75653 q = 1) (hb : d93292 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75653, d93292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75653, d93292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75654 q = 1) (hb : d93293 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75654, d93293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75654, d93293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75661 q = 1) (hb : d93300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75661, d93300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75661, d93300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21589 q ha hb
  have h17 (q : Pattern) (ha : d75662 q = 1) (hb : d93301 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75662, d93301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75662, d93301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d75663 q = 1) (hb : d93302 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75663, d93302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75663, d93302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d75664 q = 1) (hb : d93303 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75664, d93303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d75664, d93303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d75665 q = 1) (hb : d93304 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75665, d93304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75665, d93304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75666 q = 1) (hb : d93305 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75666, d93305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75666, d93305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro21591 (p : Pattern) (ha : d75676 p = 1) (hb : d93315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75631 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q hb ha
    | true =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d75672 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75672, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75672, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75673 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75673, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75673, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75674 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75674, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75674, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75675 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75675, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75675, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75676 q = 1) (hb : d93315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75676, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75676, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21592 (p : Pattern) (ha : d75683 p = 1) (hb : d93322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75631 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q hb ha
    | true =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d75672 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75672, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75672, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75673 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75673, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75673, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75674 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75674, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75674, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75675 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75675, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75675, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75637 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75637, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18944 q hb ha
    | true =>
      simp only [d75637, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d75679 q = 1) (hb : d93318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75679, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75679, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75680 q = 1) (hb : d93319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75680, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75680, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d75681 q = 1) (hb : d93320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75681, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75681, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75682 q = 1) (hb : d93321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75682, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75682, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75683 q = 1) (hb : d93322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75683, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75683, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21593 (p : Pattern) (ha : d8479 p = 1) (hb : d75702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d52130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18937 q ha hb
    | true =>
      simp only [d8314, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d52131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d75699 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d75699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d75699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d75700 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d75700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d75700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d75701 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d75701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d75701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8479 q = 1) (hb : d75702 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8479, d75702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8479, d75702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21594 (p : Pattern) (ha : d75688 p = 1) (hb : d93327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18922 q ha hb
    | true =>
      simp only [d6740, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d75687 q = 1) (hb : d93326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75687, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75687, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75688 q = 1) (hb : d93327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75688, d93327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75688, d93327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21595 (p : Pattern) (ha : d75695 p = 1) (hb : d93334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18922 q ha hb
    | true =>
      simp only [d6740, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d75693 q = 1) (hb : d93332 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75693, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75693, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d75694 q = 1) (hb : d93333 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75694, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75694, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75695 q = 1) (hb : d93334 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75695, d93334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75695, d93334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21596 (p : Pattern) (ha : d75708 p = 1) (hb : d93343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75689 q = 1) (hb : d93328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75689, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21594 q ha hb
    | true =>
      simp only [d75689, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d75690 q = 1) (hb : d93329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75690, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75690, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75691 q = 1) (hb : d93330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75691, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75691, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75692 q = 1) (hb : d93331 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75692, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75692, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75696 q = 1) (hb : d93335 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75696, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21595 q ha hb
    | true =>
      simp only [d75696, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d75697 q = 1) (hb : d93336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75697, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75697, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75698 q = 1) (hb : d93337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75698, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75698, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75703 q = 1) (hb : d93338 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75703, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21593 q hb ha
    | true =>
      simp only [d75703, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75704 q = 1) (hb : d93339 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75704, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75704, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8335 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q ha hb
    | true =>
      simp only [d8335, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8336 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8336, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75705 q = 1) (hb : d93340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75705, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75705, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75706 q = 1) (hb : d93341 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75706, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75706, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75707 q = 1) (hb : d93342 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75707, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75707, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75708 q = 1) (hb : d93343 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75708, d93343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75708, d93343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21597 (p : Pattern) (ha : d8501 p = 1) (hb : d75718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d52130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18937 q ha hb
    | true =>
      simp only [d8314, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d52131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d75699 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d75699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d75699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d75700 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d75700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d75700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d75701 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d75701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d75701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8501 q = 1) (hb : d75718 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8501, d75718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8501, d75718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21598 (p : Pattern) (ha : d75709 p = 1) (hb : d93344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18922 q ha hb
    | true =>
      simp only [d6740, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d75687 q = 1) (hb : d93326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75687, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75687, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75709 q = 1) (hb : d93344 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75709, d93344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75709, d93344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21599 (p : Pattern) (ha : d75714 p = 1) (hb : d93349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18922 q ha hb
    | true =>
      simp only [d6740, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d75693 q = 1) (hb : d93332 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75693, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75693, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d75694 q = 1) (hb : d93333 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75694, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75694, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75714 q = 1) (hb : d93349 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75714, d93349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75714, d93349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21600 (p : Pattern) (ha : d75724 p = 1) (hb : d93358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75689 q = 1) (hb : d93328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75689, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21594 q ha hb
    | true =>
      simp only [d75689, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d75690 q = 1) (hb : d93329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75690, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75690, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75691 q = 1) (hb : d93330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75691, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75691, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75692 q = 1) (hb : d93331 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75692, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75692, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75696 q = 1) (hb : d93335 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75696, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21595 q ha hb
    | true =>
      simp only [d75696, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d75697 q = 1) (hb : d93336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75697, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75697, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75698 q = 1) (hb : d93337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75698, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75698, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75703 q = 1) (hb : d93338 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75703, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21593 q hb ha
    | true =>
      simp only [d75703, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75704 q = 1) (hb : d93339 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75704, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75704, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8335 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q ha hb
    | true =>
      simp only [d8335, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8336 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8336, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75705 q = 1) (hb : d93340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75705, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75705, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75706 q = 1) (hb : d93341 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75706, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75706, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75707 q = 1) (hb : d93342 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75707, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75707, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75710 q = 1) (hb : d93345 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75710, d93345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21598 q ha hb
    | true =>
      simp only [d75710, d93345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d75711 q = 1) (hb : d93346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75711, d93346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75711, d93346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75712 q = 1) (hb : d93347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75712, d93347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75712, d93347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d75713 q = 1) (hb : d93348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75713, d93348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75713, d93348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d75715 q = 1) (hb : d93350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75715, d93350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21599 q ha hb
    | true =>
      simp only [d75715, d93350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d75716 q = 1) (hb : d93351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75716, d93351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75716, d93351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d75717 q = 1) (hb : d93352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75717, d93352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d75717, d93352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75719 q = 1) (hb : d93353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75719, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21597 q hb ha
    | true =>
      simp only [d75719, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18944 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d75720 q = 1) (hb : d93354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75720, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d75720, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8356 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18944 q ha hb
    | true =>
      simp only [d8356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8357 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d75721 q = 1) (hb : d93355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75721, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d75721, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d75722 q = 1) (hb : d93356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75722, d93356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d75722, d93356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d75723 q = 1) (hb : d93357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75723, d93357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75723, d93357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d75724 q = 1) (hb : d93358 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75724, d93358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75724, d93358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21601 (p : Pattern) (ha : d75726 p = 1) (hb : d93360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75631 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q hb ha
    | true =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d75672 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75672, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75672, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75673 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75673, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75673, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75674 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75674, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75674, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75675 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75675, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75675, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d75726 q = 1) (hb : d93360 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75726, d93360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75726, d93360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro21602 (p : Pattern) (ha : d75733 p = 1) (hb : d93367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75719 q = 1) (hb : d93353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75719, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21597 q hb ha
    | true =>
      simp only [d75719, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18944 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75720 q = 1) (hb : d93354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75720, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75720, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8356 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18944 q ha hb
    | true =>
      simp only [d8356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8357 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75721 q = 1) (hb : d93355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75721, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75721, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75731 q = 1) (hb : d93365 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75731, d93365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75731, d93365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75732 q = 1) (hb : d93366 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75732, d93366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75732, d93366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75733 q = 1) (hb : d93367 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75733, d93367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75733, d93367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21603 (p : Pattern) (ha : d8555 p = 1) (hb : d75742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d52190 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d52190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18947 q ha hb
    | true =>
      simp only [d8378, d52190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d52191 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d52191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d52191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8552 q = 1) (hb : d75739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8552, d75739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8552, d75739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8553 q = 1) (hb : d75740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8553, d75740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8553, d75740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8554 q = 1) (hb : d75741 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8554, d75741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8554, d75741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8555 q = 1) (hb : d75742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8555, d75742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8555, d75742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21604 (p : Pattern) (ha : d75748 p = 1) (hb : d93378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75743 q = 1) (hb : d93373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75743, d93373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21603 q hb ha
    | true =>
      simp only [d75743, d93373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18949 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75655 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75744 q = 1) (hb : d93374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75744, d93374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75744, d93374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8399 q = 1) (hb : d74104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8399, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18949 q ha hb
    | true =>
      simp only [d8399, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8400 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8400, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8400, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75745 q = 1) (hb : d93375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75745, d93375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75745, d93375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75746 q = 1) (hb : d93376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75746, d93376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75746, d93376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75747 q = 1) (hb : d93377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75747, d93377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75747, d93377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75748 q = 1) (hb : d93378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75748, d93378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75748, d93378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21605 (p : Pattern) (ha : d75754 p = 1) (hb : d93384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75677 q = 1) (hb : d93316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75677, d93316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75677, d93316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21591 q ha hb
  have h2 (q : Pattern) (ha : d75678 q = 1) (hb : d93317 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75678, d93317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75678, d93317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75684 q = 1) (hb : d93323 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75684, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21591 q ha hb
    | true =>
      simp only [d75684, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21592 q ha hb
  have h4 (q : Pattern) (ha : d75685 q = 1) (hb : d93324 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75685, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75685, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75686 q = 1) (hb : d93325 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75686, d93325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75686, d93325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75725 q = 1) (hb : d93359 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75725, d93359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21596 q ha hb
    | true =>
      simp only [d75725, d93359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21600 q ha hb
  have h7 (q : Pattern) (ha : d75727 q = 1) (hb : d93361 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75727, d93361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21601 q ha hb
    | true =>
      simp only [d75727, d93361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d75728 q = 1) (hb : d93362 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75728, d93362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75728, d93362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75729 q = 1) (hb : d93363 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75729, d93363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75729, d93363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75730 q = 1) (hb : d93364 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75730, d93364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75730, d93364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75734 q = 1) (hb : d93368 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75734, d93368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75734, d93368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21602 q ha hb
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
  have h13 (q : Pattern) (ha : d75735 q = 1) (hb : d93369 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75735, d93369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d75735, d93369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75736 q = 1) (hb : d93370 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75736, d93370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75736, d93370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75737 q = 1) (hb : d93371 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75737, d93371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d75737, d93371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75738 q = 1) (hb : d93372 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75738, d93372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75738, d93372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75749 q = 1) (hb : d93379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75749, d93379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75749, d93379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21604 q ha hb
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
  have h19 (q : Pattern) (ha : d75750 q = 1) (hb : d93380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75750, d93380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75750, d93380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75751 q = 1) (hb : d93381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75751, d93381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75751, d93381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75752 q = 1) (hb : d93382 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75752, d93382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d75752, d93382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75753 q = 1) (hb : d93383 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75753, d93383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d75753, d93383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75754 q = 1) (hb : d93384 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75754, d93384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75754, d93384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21606 (p : Pattern) (ha : d75760 p = 1) (hb : d93390 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d75667 q = 1) (hb : d93306 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75667, d93306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75667, d93306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21590 q ha hb
  have h6 (q : Pattern) (ha : d75668 q = 1) (hb : d93307 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75668, d93307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75668, d93307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75669 q = 1) (hb : d93308 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75669, d93308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75669, d93308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75670 q = 1) (hb : d93309 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75670, d93309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75670, d93309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75671 q = 1) (hb : d93310 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75671, d93310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75671, d93310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75755 q = 1) (hb : d93385 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75755, d93385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75755, d93385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21605 q ha hb
  have h11 (q : Pattern) (ha : d75756 q = 1) (hb : d93386 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75756, d93386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75756, d93386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d75757 q = 1) (hb : d93387 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75757, d93387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75757, d93387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d75758 q = 1) (hb : d93388 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75758, d93388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75758, d93388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d75759 q = 1) (hb : d93389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75759, d93389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75759, d93389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75760 q = 1) (hb : d93390 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75760, d93390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d75760, d93390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21607 (p : Pattern) (ha : d75766 p = 1) (hb : d93396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75761 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75761, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18965 q hb ha
    | true =>
      simp only [d75761, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d75762 q = 1) (hb : d93392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75762, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75762, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75763 q = 1) (hb : d93393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75763, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75763, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75764 q = 1) (hb : d93394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75764, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75764, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75765 q = 1) (hb : d93395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75765, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75765, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75766 q = 1) (hb : d93396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75766, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75766, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21608 (p : Pattern) (ha : d75774 p = 1) (hb : d93404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75761 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75761, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18965 q hb ha
    | true =>
      simp only [d75761, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d75762 q = 1) (hb : d93392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75762, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75762, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75763 q = 1) (hb : d93393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75763, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75763, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75764 q = 1) (hb : d93394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75764, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75764, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75765 q = 1) (hb : d93395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75765, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75765, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75769 q = 1) (hb : d93399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75769, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18971 q hb ha
    | true =>
      simp only [d75769, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h7 (q : Pattern) (ha : d75770 q = 1) (hb : d93400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75770, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75770, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75771 q = 1) (hb : d93401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75771, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75771, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d75772 q = 1) (hb : d93402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75772, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75772, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75773 q = 1) (hb : d93403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75773, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75773, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75774 q = 1) (hb : d93404 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75774, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75774, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21609 (p : Pattern) (ha : d68926 p = 1) (hb : d93427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d68921 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18958 q ha hb
    | true =>
      simp only [d6800, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d68922 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68923 q = 1) (hb : d93424 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d68923, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68923, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68924 q = 1) (hb : d93425 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d68924, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68924, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68925 q = 1) (hb : d93426 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d68925, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68925, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68926 q = 1) (hb : d93427 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d68926, d93427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68926, d93427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21610 (p : Pattern) (ha : d75779 p = 1) (hb : d93409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18953 q ha hb
    | true =>
      simp only [d8314, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d74122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d74123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d75778 q = 1) (hb : d93408 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75778, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75778, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75779 q = 1) (hb : d93409 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75779, d93409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75779, d93409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21611 (p : Pattern) (ha : d75786 p = 1) (hb : d93416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18953 q ha hb
    | true =>
      simp only [d8314, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d74122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d75784 q = 1) (hb : d93414 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75784, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75784, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d75785 q = 1) (hb : d93415 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75785, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75785, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75786 q = 1) (hb : d93416 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75786, d93416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75786, d93416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21612 (p : Pattern) (ha : d75793 p = 1) (hb : d93423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d52302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18963 q ha hb
    | true =>
      simp only [d8454, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d52303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75790 q = 1) (hb : d93420 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d75790, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75790, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75791 q = 1) (hb : d93421 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75791, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75791, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75792 q = 1) (hb : d93422 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75792, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75792, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75793 q = 1) (hb : d93423 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75793, d93423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75793, d93423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21613 (p : Pattern) (ha : d75799 p = 1) (hb : d93433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75780 q = 1) (hb : d93410 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75780, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21610 q ha hb
    | true =>
      simp only [d75780, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q hb ha
  have h2 (q : Pattern) (ha : d75781 q = 1) (hb : d93411 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75781, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75781, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75782 q = 1) (hb : d93412 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75782, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75782, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75783 q = 1) (hb : d93413 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75783, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75783, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75787 q = 1) (hb : d93417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75787, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21611 q ha hb
    | true =>
      simp only [d75787, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q hb ha
  have h6 (q : Pattern) (ha : d75788 q = 1) (hb : d93418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75788, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75788, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75789 q = 1) (hb : d93419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75789, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75789, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75794 q = 1) (hb : d93428 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75794, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21612 q ha hb
    | true =>
      simp only [d75794, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21609 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75761 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75795 q = 1) (hb : d93429 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75795, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75795, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8480 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18965 q ha hb
    | true =>
      simp only [d8480, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8481 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8481, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75796 q = 1) (hb : d93430 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75796, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75796, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75797 q = 1) (hb : d93431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75797, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75797, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75798 q = 1) (hb : d93432 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75798, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75798, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75799 q = 1) (hb : d93433 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75799, d93433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75799, d93433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21614 (p : Pattern) (ha : d75800 p = 1) (hb : d93434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18953 q ha hb
    | true =>
      simp only [d8314, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d74122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d74123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d75778 q = 1) (hb : d93408 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75778, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75778, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75800 q = 1) (hb : d93434 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75800, d93434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75800, d93434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21615 (p : Pattern) (ha : d75805 p = 1) (hb : d93439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18953 q ha hb
    | true =>
      simp only [d8314, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d74122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d75784 q = 1) (hb : d93414 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75784, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75784, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d75785 q = 1) (hb : d93415 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75785, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75785, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75805 q = 1) (hb : d93439 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75805, d93439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75805, d93439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21616 (p : Pattern) (ha : d75809 p = 1) (hb : d93443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d52302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18963 q ha hb
    | true =>
      simp only [d8454, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d52303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75790 q = 1) (hb : d93420 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d75790, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75790, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75791 q = 1) (hb : d93421 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75791, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75791, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75792 q = 1) (hb : d93422 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75792, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75792, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75809 q = 1) (hb : d93443 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75809, d93443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75809, d93443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21617 (p : Pattern) (ha : d75810 p = 1) (hb : d93444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d68921 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18958 q ha hb
    | true =>
      simp only [d6800, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d68922 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68923 q = 1) (hb : d93424 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d68923, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68923, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68924 q = 1) (hb : d93425 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d68924, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68924, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68925 q = 1) (hb : d93426 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d68925, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68925, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75810 q = 1) (hb : d93444 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75810, d93444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75810, d93444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21618 (p : Pattern) (ha : d75816 p = 1) (hb : d93450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75780 q = 1) (hb : d93410 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75780, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21610 q ha hb
    | true =>
      simp only [d75780, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q hb ha
  have h2 (q : Pattern) (ha : d75781 q = 1) (hb : d93411 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75781, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75781, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75782 q = 1) (hb : d93412 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75782, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75782, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75783 q = 1) (hb : d93413 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75783, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75783, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75787 q = 1) (hb : d93417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75787, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21611 q ha hb
    | true =>
      simp only [d75787, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q hb ha
  have h6 (q : Pattern) (ha : d75788 q = 1) (hb : d93418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75788, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75788, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75789 q = 1) (hb : d93419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75789, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75789, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75794 q = 1) (hb : d93428 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75794, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21612 q ha hb
    | true =>
      simp only [d75794, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21609 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75761 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75795 q = 1) (hb : d93429 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75795, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75795, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8480 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18965 q ha hb
    | true =>
      simp only [d8480, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8481 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8481, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75796 q = 1) (hb : d93430 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75796, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75796, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75797 q = 1) (hb : d93431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75797, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75797, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75798 q = 1) (hb : d93432 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75798, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75798, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75801 q = 1) (hb : d93435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75801, d93435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21614 q ha hb
    | true =>
      simp only [d75801, d93435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94 q hb ha
  have h17 (q : Pattern) (ha : d75802 q = 1) (hb : d93436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75802, d93436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75802, d93436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75803 q = 1) (hb : d93437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75803, d93437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75803, d93437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d75804 q = 1) (hb : d93438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75804, d93438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75804, d93438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d75806 q = 1) (hb : d93440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75806, d93440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21615 q ha hb
    | true =>
      simp only [d75806, d93440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q hb ha
  have h21 (q : Pattern) (ha : d75807 q = 1) (hb : d93441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75807, d93441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75807, d93441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d75808 q = 1) (hb : d93442 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75808, d93442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d75808, d93442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75811 q = 1) (hb : d93445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75811, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21616 q ha hb
    | true =>
      simp only [d75811, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21617 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d75769 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d75812 q = 1) (hb : d93446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75812, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d75812, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8502 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18971 q ha hb
    | true =>
      simp only [d8502, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8503 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8503, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d75813 q = 1) (hb : d93447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75813, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d75813, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d75814 q = 1) (hb : d93448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75814, d93448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d75814, d93448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d75815 q = 1) (hb : d93449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75815, d93449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75815, d93449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d75816 q = 1) (hb : d93450 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75816, d93450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75816, d93450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21619 (p : Pattern) (ha : d75823 p = 1) (hb : d93457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75818 q = 1) (hb : d93452 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75818, d93452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21609 q ha hb
    | true =>
      simp only [d75818, d93452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d75819 q = 1) (hb : d93453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75819, d93453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75819, d93453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75820 q = 1) (hb : d93454 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75820, d93454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75820, d93454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75821 q = 1) (hb : d93455 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75821, d93455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75821, d93455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75822 q = 1) (hb : d93456 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75822, d93456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75822, d93456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d75823 q = 1) (hb : d93457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75823, d93457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75823, d93457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro21620 (p : Pattern) (ha : d75830 p = 1) (hb : d93464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75811 q = 1) (hb : d93445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75811, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21616 q ha hb
    | true =>
      simp only [d75811, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21617 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75769 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75812 q = 1) (hb : d93446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75812, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75812, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8502 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18971 q ha hb
    | true =>
      simp only [d8502, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8503 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8503, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75813 q = 1) (hb : d93447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75813, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75813, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75828 q = 1) (hb : d93462 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75828, d93462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75828, d93462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75829 q = 1) (hb : d93463 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75829, d93463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75829, d93463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75830 q = 1) (hb : d93464 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75830, d93464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75830, d93464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21621 (p : Pattern) (ha : d75839 p = 1) (hb : d93473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8530 q = 1) (hb : d52375 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8530, d52375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18974 q ha hb
    | true =>
      simp only [d8530, d52375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8531 q = 1) (hb : d52376 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8531, d52376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8531, d52376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75836 q = 1) (hb : d93470 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d75836, d93470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75836, d93470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75837 q = 1) (hb : d93471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75837, d93471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75837, d93471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75838 q = 1) (hb : d93472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75838, d93472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75838, d93472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75839 q = 1) (hb : d93473 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75839, d93473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75839, d93473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21622 (p : Pattern) (ha : d75852 p = 1) (hb : d93477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6846 q = 1) (hb : d75847 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d75847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18976 q ha hb
    | true =>
      simp only [d6846, d75847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6847 q = 1) (hb : d75848 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d75848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d75848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75849 q = 1) (hb : d93474 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d75849, d93474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75849, d93474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75850 q = 1) (hb : d93475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75850, d93475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75850, d93475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75851 q = 1) (hb : d93476 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75851, d93476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75851, d93476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75852 q = 1) (hb : d93477 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75852, d93477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75852, d93477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21623 (p : Pattern) (ha : d75859 p = 1) (hb : d93483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75853 q = 1) (hb : d93478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75853, d93478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21621 q ha hb
    | true =>
      simp only [d75853, d93478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21622 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75854 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75855 q = 1) (hb : d93479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75855, d93479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75855, d93479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8556 q = 1) (hb : d74155 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8556, d74155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18979 q ha hb
    | true =>
      simp only [d8556, d74155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8557 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8557, d74156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8557, d74156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75856 q = 1) (hb : d93480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75856, d93480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75856, d93480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75857 q = 1) (hb : d93481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75857, d93481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75857, d93481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75858 q = 1) (hb : d93482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75858, d93482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75858, d93482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75859 q = 1) (hb : d93483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75859, d93483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75859, d93483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21624 (p : Pattern) (ha : d75865 p = 1) (hb : d93489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75767 q = 1) (hb : d93397 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75767, d93397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75767, d93397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21607 q ha hb
  have h2 (q : Pattern) (ha : d75768 q = 1) (hb : d93398 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75768, d93398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75768, d93398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75775 q = 1) (hb : d93405 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75775, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21607 q ha hb
    | true =>
      simp only [d75775, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21608 q ha hb
  have h4 (q : Pattern) (ha : d75776 q = 1) (hb : d93406 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75776, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75776, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75777 q = 1) (hb : d93407 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75777, d93407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75777, d93407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75817 q = 1) (hb : d93451 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75817, d93451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21613 q ha hb
    | true =>
      simp only [d75817, d93451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21618 q ha hb
  have h7 (q : Pattern) (ha : d75824 q = 1) (hb : d93458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75824, d93458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21619 q ha hb
    | true =>
      simp only [d75824, d93458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q hb ha
  have h8 (q : Pattern) (ha : d75825 q = 1) (hb : d93459 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75825, d93459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75825, d93459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75826 q = 1) (hb : d93460 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75826, d93460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75826, d93460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75827 q = 1) (hb : d93461 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75827, d93461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75827, d93461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75831 q = 1) (hb : d93465 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75831, d93465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75831, d93465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21620 q ha hb
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
  have h13 (q : Pattern) (ha : d75832 q = 1) (hb : d93466 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75832, d93466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d75832, d93466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75833 q = 1) (hb : d93467 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75833, d93467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75833, d93467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75834 q = 1) (hb : d93468 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75834, d93468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d75834, d93468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75835 q = 1) (hb : d93469 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75835, d93469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75835, d93469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75860 q = 1) (hb : d93484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75860, d93484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75860, d93484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21623 q ha hb
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
  have h19 (q : Pattern) (ha : d75861 q = 1) (hb : d93485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75861, d93485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75861, d93485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75862 q = 1) (hb : d93486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75862, d93486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75862, d93486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75863 q = 1) (hb : d93487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75863, d93487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d75863, d93487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75864 q = 1) (hb : d93488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75864, d93488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d75864, d93488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75865 q = 1) (hb : d93489 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75865, d93489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75865, d93489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21625 (p : Pattern) (ha : d75871 p = 1) (hb : d93495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75866 q = 1) (hb : d93490 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75866, d93490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75866, d93490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21624 q ha hb
  have h2 (q : Pattern) (ha : d75867 q = 1) (hb : d93491 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75867, d93491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75867, d93491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75868 q = 1) (hb : d93492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75868, d93492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75868, d93492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75869 q = 1) (hb : d93493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75869, d93493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75869, d93493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75870 q = 1) (hb : d93494 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75870, d93494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75870, d93494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75871 q = 1) (hb : d93495 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75871, d93495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75871, d93495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21626 (p : Pattern) (ha : d75882 p = 1) (hb : d93502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75877 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75877, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18995 q hb ha
    | true =>
      simp only [d75877, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d75878 q = 1) (hb : d93498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75878, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75878, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75879 q = 1) (hb : d93499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75879, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75879, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75880 q = 1) (hb : d93500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75880, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75880, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75881 q = 1) (hb : d93501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75881, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75881, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75882 q = 1) (hb : d93502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75882, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75882, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21627 (p : Pattern) (ha : d75891 p = 1) (hb : d93510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75877 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75877, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18995 q hb ha
    | true =>
      simp only [d75877, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d75878 q = 1) (hb : d93498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75878, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75878, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75879 q = 1) (hb : d93499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75879, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75879, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75880 q = 1) (hb : d93500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75880, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75880, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75881 q = 1) (hb : d93501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75881, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75881, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75886 q = 1) (hb : d93505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75886, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19001 q hb ha
    | true =>
      simp only [d75886, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h7 (q : Pattern) (ha : d75887 q = 1) (hb : d93506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75887, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75887, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75888 q = 1) (hb : d93507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75888, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75888, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d75889 q = 1) (hb : d93508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75889, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75889, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75890 q = 1) (hb : d93509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75890, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75890, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75891 q = 1) (hb : d93510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75891, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75891, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21628 (p : Pattern) (ha : d69018 p = 1) (hb : d93533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d69013 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18988 q ha hb
    | true =>
      simp only [d6878, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d69014 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69015 q = 1) (hb : d93530 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d69015, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69015, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69016 q = 1) (hb : d93531 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d69016, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69016, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69017 q = 1) (hb : d93532 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d69017, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69017, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69018 q = 1) (hb : d93533 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d69018, d93533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69018, d93533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21629 (p : Pattern) (ha : d75896 p = 1) (hb : d93515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18983 q ha hb
    | true =>
      simp only [d8577, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d75873 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d75873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d75873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d75874 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d75874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d75874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d75895 q = 1) (hb : d93514 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75895, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75895, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75896 q = 1) (hb : d93515 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75896, d93515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75896, d93515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21630 (p : Pattern) (ha : d75903 p = 1) (hb : d93522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18983 q ha hb
    | true =>
      simp only [d8577, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d75873 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d75873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d75873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d75901 q = 1) (hb : d93520 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75901, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75901, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d75902 q = 1) (hb : d93521 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75902, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75902, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75903 q = 1) (hb : d93522 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75903, d93522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75903, d93522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21631 (p : Pattern) (ha : d75910 p = 1) (hb : d93529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d52523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18993 q ha hb
    | true =>
      simp only [d8616, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d52524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75907 q = 1) (hb : d93526 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d75907, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75907, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75908 q = 1) (hb : d93527 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75908, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75908, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75909 q = 1) (hb : d93528 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75909, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75909, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75910 q = 1) (hb : d93529 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75910, d93529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75910, d93529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21632 (p : Pattern) (ha : d75918 p = 1) (hb : d93539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75897 q = 1) (hb : d93516 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75897, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21629 q ha hb
    | true =>
      simp only [d75897, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q hb ha
  have h2 (q : Pattern) (ha : d75898 q = 1) (hb : d93517 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75898, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75898, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75899 q = 1) (hb : d93518 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75899, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75899, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75900 q = 1) (hb : d93519 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75900, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75900, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75904 q = 1) (hb : d93523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75904, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21630 q ha hb
    | true =>
      simp only [d75904, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q hb ha
  have h6 (q : Pattern) (ha : d75905 q = 1) (hb : d93524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75905, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75905, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75906 q = 1) (hb : d93525 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75906, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75906, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75911 q = 1) (hb : d93534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75911, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21631 q ha hb
    | true =>
      simp only [d75911, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21628 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75877 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75912 q = 1) (hb : d93535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75912, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75912, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8642 q = 1) (hb : d75913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18995 q ha hb
    | true =>
      simp only [d8642, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8643 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8643, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75915 q = 1) (hb : d93536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75915, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75915, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75916 q = 1) (hb : d93537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75916, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75916, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75917 q = 1) (hb : d93538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75917, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75917, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75918 q = 1) (hb : d93539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75918, d93539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75918, d93539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21633 (p : Pattern) (ha : d75919 p = 1) (hb : d93540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18983 q ha hb
    | true =>
      simp only [d8577, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d75873 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d75873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d75873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d75874 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d75874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d75874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d75895 q = 1) (hb : d93514 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75895, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75895, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75919 q = 1) (hb : d93540 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75919, d93540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75919, d93540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21634 (p : Pattern) (ha : d75924 p = 1) (hb : d93545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18983 q ha hb
    | true =>
      simp only [d8577, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d75873 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d75873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d75873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d75901 q = 1) (hb : d93520 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75901, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75901, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d75902 q = 1) (hb : d93521 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75902, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75902, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75924 q = 1) (hb : d93545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75924, d93545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75924, d93545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21635 (p : Pattern) (ha : d75928 p = 1) (hb : d93549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d52523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18993 q ha hb
    | true =>
      simp only [d8616, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d52524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75907 q = 1) (hb : d93526 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d75907, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75907, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75908 q = 1) (hb : d93527 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75908, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75908, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75909 q = 1) (hb : d93528 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75909, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75909, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75928 q = 1) (hb : d93549 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75928, d93549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75928, d93549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21636 (p : Pattern) (ha : d75929 p = 1) (hb : d93550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d69013 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18988 q ha hb
    | true =>
      simp only [d6878, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d69014 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69015 q = 1) (hb : d93530 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d69015, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69015, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69016 q = 1) (hb : d93531 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d69016, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69016, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69017 q = 1) (hb : d93532 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d69017, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69017, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75929 q = 1) (hb : d93550 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75929, d93550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75929, d93550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21637 (p : Pattern) (ha : d75937 p = 1) (hb : d93556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75897 q = 1) (hb : d93516 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75897, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21629 q ha hb
    | true =>
      simp only [d75897, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q hb ha
  have h2 (q : Pattern) (ha : d75898 q = 1) (hb : d93517 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75898, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75898, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75899 q = 1) (hb : d93518 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75899, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75899, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75900 q = 1) (hb : d93519 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75900, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75900, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75904 q = 1) (hb : d93523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75904, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21630 q ha hb
    | true =>
      simp only [d75904, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q hb ha
  have h6 (q : Pattern) (ha : d75905 q = 1) (hb : d93524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75905, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75905, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75906 q = 1) (hb : d93525 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75906, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75906, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75911 q = 1) (hb : d93534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75911, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21631 q ha hb
    | true =>
      simp only [d75911, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21628 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75877 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75912 q = 1) (hb : d93535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75912, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75912, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8642 q = 1) (hb : d75913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18995 q ha hb
    | true =>
      simp only [d8642, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8643 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8643, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75915 q = 1) (hb : d93536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75915, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75915, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75916 q = 1) (hb : d93537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75916, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75916, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75917 q = 1) (hb : d93538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75917, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75917, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75920 q = 1) (hb : d93541 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75920, d93541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21633 q ha hb
    | true =>
      simp only [d75920, d93541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro141 q hb ha
  have h17 (q : Pattern) (ha : d75921 q = 1) (hb : d93542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75921, d93542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75921, d93542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75922 q = 1) (hb : d93543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75922, d93543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75922, d93543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d75923 q = 1) (hb : d93544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75923, d93544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75923, d93544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d75925 q = 1) (hb : d93546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75925, d93546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21634 q ha hb
    | true =>
      simp only [d75925, d93546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q hb ha
  have h21 (q : Pattern) (ha : d75926 q = 1) (hb : d93547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75926, d93547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75926, d93547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d75927 q = 1) (hb : d93548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75927, d93548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d75927, d93548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75930 q = 1) (hb : d93551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75930, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21635 q ha hb
    | true =>
      simp only [d75930, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21636 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d75886 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d75931 q = 1) (hb : d93552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75931, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d75931, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8664 q = 1) (hb : d75932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19001 q ha hb
    | true =>
      simp only [d8664, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8665 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8665, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d75934 q = 1) (hb : d93553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75934, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d75934, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d75935 q = 1) (hb : d93554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75935, d93554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d75935, d93554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d75936 q = 1) (hb : d93555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75936, d93555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75936, d93555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d75937 q = 1) (hb : d93556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75937, d93556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75937, d93556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21638 (p : Pattern) (ha : d75944 p = 1) (hb : d93563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75939 q = 1) (hb : d93558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75939, d93558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21628 q ha hb
    | true =>
      simp only [d75939, d93558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d75940 q = 1) (hb : d93559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75940, d93559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75940, d93559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75941 q = 1) (hb : d93560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75941, d93560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75941, d93560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75942 q = 1) (hb : d93561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75942, d93561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75942, d93561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75943 q = 1) (hb : d93562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75943, d93562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75943, d93562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d75944 q = 1) (hb : d93563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75944, d93563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75944, d93563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro21639 (p : Pattern) (ha : d75951 p = 1) (hb : d93570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75930 q = 1) (hb : d93551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75930, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21635 q ha hb
    | true =>
      simp only [d75930, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21636 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75886 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75931 q = 1) (hb : d93552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75931, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75931, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8664 q = 1) (hb : d75932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19001 q ha hb
    | true =>
      simp only [d8664, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8665 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8665, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75934 q = 1) (hb : d93553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75934, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75934, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75949 q = 1) (hb : d93568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75949, d93568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75949, d93568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75950 q = 1) (hb : d93569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75950, d93569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75950, d93569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75951 q = 1) (hb : d93570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75951, d93570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75951, d93570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21640 (p : Pattern) (ha : d75960 p = 1) (hb : d93579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8692 q = 1) (hb : d52612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8692, d52612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19004 q ha hb
    | true =>
      simp only [d8692, d52612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8693 q = 1) (hb : d52613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8693, d52613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8693, d52613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75957 q = 1) (hb : d93576 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d75957, d93576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75957, d93576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75958 q = 1) (hb : d93577 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75958, d93577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75958, d93577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75959 q = 1) (hb : d93578 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75959, d93578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75959, d93578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75960 q = 1) (hb : d93579 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75960, d93579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75960, d93579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21641 (p : Pattern) (ha : d75973 p = 1) (hb : d93583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6924 q = 1) (hb : d75968 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d75968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19006 q ha hb
    | true =>
      simp only [d6924, d75968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6925 q = 1) (hb : d75969 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d75969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d75969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75970 q = 1) (hb : d93580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d75970, d93580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75970, d93580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75971 q = 1) (hb : d93581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d75971, d93581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75971, d93581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75972 q = 1) (hb : d93582 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d75972, d93582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75972, d93582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75973 q = 1) (hb : d93583 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d75973, d93583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75973, d93583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21642 (p : Pattern) (ha : d75986 p = 1) (hb : d93589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75974 q = 1) (hb : d93584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75974, d93584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21640 q ha hb
    | true =>
      simp only [d75974, d93584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21641 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75979 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75980 q = 1) (hb : d93585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75980, d93585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75980, d93585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8722 q = 1) (hb : d75981 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8722, d75981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19009 q ha hb
    | true =>
      simp only [d8722, d75981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8723 q = 1) (hb : d75982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8723, d75982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8723, d75982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75983 q = 1) (hb : d93586 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75983, d93586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75983, d93586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75984 q = 1) (hb : d93587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75984, d93587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75984, d93587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75985 q = 1) (hb : d93588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75985, d93588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75985, d93588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75986 q = 1) (hb : d93589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75986, d93589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75986, d93589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21643 (p : Pattern) (ha : d75992 p = 1) (hb : d93595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75883 q = 1) (hb : d93503 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75883, d93503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75883, d93503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21626 q ha hb
  have h2 (q : Pattern) (ha : d75884 q = 1) (hb : d93504 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75884, d93504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75884, d93504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75892 q = 1) (hb : d93511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75892, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21626 q ha hb
    | true =>
      simp only [d75892, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21627 q ha hb
  have h4 (q : Pattern) (ha : d75893 q = 1) (hb : d93512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75893, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75893, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75894 q = 1) (hb : d93513 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75894, d93513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75894, d93513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75938 q = 1) (hb : d93557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75938, d93557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21632 q ha hb
    | true =>
      simp only [d75938, d93557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21637 q ha hb
  have h7 (q : Pattern) (ha : d75945 q = 1) (hb : d93564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75945, d93564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21638 q ha hb
    | true =>
      simp only [d75945, d93564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q hb ha
  have h8 (q : Pattern) (ha : d75946 q = 1) (hb : d93565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75946, d93565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75946, d93565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75947 q = 1) (hb : d93566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75947, d93566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75947, d93566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75948 q = 1) (hb : d93567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75948, d93567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75948, d93567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75952 q = 1) (hb : d93571 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75952, d93571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75952, d93571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21639 q ha hb
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
  have h13 (q : Pattern) (ha : d75953 q = 1) (hb : d93572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75953, d93572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d75953, d93572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75954 q = 1) (hb : d93573 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75954, d93573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75954, d93573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75955 q = 1) (hb : d93574 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75955, d93574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d75955, d93574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75956 q = 1) (hb : d93575 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75956, d93575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75956, d93575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75987 q = 1) (hb : d93590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75987, d93590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75987, d93590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21642 q ha hb
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
  have h19 (q : Pattern) (ha : d75988 q = 1) (hb : d93591 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75988, d93591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75988, d93591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75989 q = 1) (hb : d93592 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75989, d93592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75989, d93592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75990 q = 1) (hb : d93593 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75990, d93593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d75990, d93593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75991 q = 1) (hb : d93594 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75991, d93594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d75991, d93594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75992 q = 1) (hb : d93595 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75992, d93595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75992, d93595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21644 (p : Pattern) (ha : d75998 p = 1) (hb : d93601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75993 q = 1) (hb : d93596 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75993, d93596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75993, d93596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21643 q ha hb
  have h2 (q : Pattern) (ha : d75994 q = 1) (hb : d93597 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75994, d93597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75994, d93597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75995 q = 1) (hb : d93598 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75995, d93598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75995, d93598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75996 q = 1) (hb : d93599 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75996, d93599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75996, d93599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75997 q = 1) (hb : d93600 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75997, d93600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75997, d93600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75998 q = 1) (hb : d93601 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75998, d93601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75998, d93601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21645 (p : Pattern) (ha : d76010 p = 1) (hb : d93609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76005 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76005, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19025 q hb ha
    | true =>
      simp only [d76005, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d76006 q = 1) (hb : d93605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76006, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76006, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76007 q = 1) (hb : d93606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76007, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76007, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76008 q = 1) (hb : d93607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76008, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76008, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76009 q = 1) (hb : d93608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76009, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76009, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76010 q = 1) (hb : d93609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76010, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76010, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21646 (p : Pattern) (ha : d76019 p = 1) (hb : d93617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76005 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76005, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19025 q hb ha
    | true =>
      simp only [d76005, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d76006 q = 1) (hb : d93605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76006, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76006, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76007 q = 1) (hb : d93606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76007, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76007, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76008 q = 1) (hb : d93607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76008, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76008, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76009 q = 1) (hb : d93608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76009, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76009, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76014 q = 1) (hb : d93612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76014, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19031 q hb ha
    | true =>
      simp only [d76014, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h7 (q : Pattern) (ha : d76015 q = 1) (hb : d93613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76015, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76015, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76016 q = 1) (hb : d93614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76016, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76016, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d76017 q = 1) (hb : d93615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76017, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76017, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76018 q = 1) (hb : d93616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76018, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76018, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76019 q = 1) (hb : d93617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76019, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76019, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21647 (p : Pattern) (ha : d69125 p = 1) (hb : d93640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d69120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19018 q ha hb
    | true =>
      simp only [d6957, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d69121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69122 q = 1) (hb : d93637 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d69122, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69122, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69123 q = 1) (hb : d93638 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d69123, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69123, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69124 q = 1) (hb : d93639 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d69124, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69124, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69125 q = 1) (hb : d93640 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d69125, d93640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69125, d93640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21648 (p : Pattern) (ha : d76024 p = 1) (hb : d93622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d76001 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d76002 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d76002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d76002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76023 q = 1) (hb : d93621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76023, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76023, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76024 q = 1) (hb : d93622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76024, d93622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76024, d93622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21649 (p : Pattern) (ha : d76031 p = 1) (hb : d93629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d76001 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d76029 q = 1) (hb : d93627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76029, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76029, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d76030 q = 1) (hb : d93628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76030, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76030, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76031 q = 1) (hb : d93629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76031, d93629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76031, d93629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21650 (p : Pattern) (ha : d76038 p = 1) (hb : d93636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d52803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19023 q ha hb
    | true =>
      simp only [d8783, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d52804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76035 q = 1) (hb : d93633 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76035, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76035, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76036 q = 1) (hb : d93634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76036, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76036, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76037 q = 1) (hb : d93635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76037, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76037, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76038 q = 1) (hb : d93636 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76038, d93636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76038, d93636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21651 (p : Pattern) (ha : d76046 p = 1) (hb : d93646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76025 q = 1) (hb : d93623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76025, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21648 q ha hb
    | true =>
      simp only [d76025, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q hb ha
  have h2 (q : Pattern) (ha : d76026 q = 1) (hb : d93624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76026, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76026, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76027 q = 1) (hb : d93625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76027, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76027, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76028 q = 1) (hb : d93626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76028, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76028, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76032 q = 1) (hb : d93630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76032, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21649 q ha hb
    | true =>
      simp only [d76032, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q hb ha
  have h6 (q : Pattern) (ha : d76033 q = 1) (hb : d93631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76033, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76033, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76034 q = 1) (hb : d93632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76034, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76034, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d76039 q = 1) (hb : d93641 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76039, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21650 q ha hb
    | true =>
      simp only [d76039, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21647 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76005 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76040 q = 1) (hb : d93642 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76040, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76040, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8809 q = 1) (hb : d76041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19025 q ha hb
    | true =>
      simp only [d8809, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8810 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8810, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76043 q = 1) (hb : d93643 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76043, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76043, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76044 q = 1) (hb : d93644 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76044, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76044, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76045 q = 1) (hb : d93645 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76045, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76045, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76046 q = 1) (hb : d93646 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76046, d93646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76046, d93646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21652 (p : Pattern) (ha : d76047 p = 1) (hb : d93647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d76001 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d76002 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d76002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d76002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76023 q = 1) (hb : d93621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76023, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76023, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76047 q = 1) (hb : d93647 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76047, d93647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76047, d93647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21653 (p : Pattern) (ha : d76052 p = 1) (hb : d93652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19013 q ha hb
    | true =>
      simp only [d8744, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d76001 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d76001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d76029 q = 1) (hb : d93627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76029, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76029, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d76030 q = 1) (hb : d93628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76030, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76030, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76052 q = 1) (hb : d93652 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76052, d93652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76052, d93652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21654 (p : Pattern) (ha : d76056 p = 1) (hb : d93656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d52803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19023 q ha hb
    | true =>
      simp only [d8783, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d52804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76035 q = 1) (hb : d93633 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76035, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76035, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76036 q = 1) (hb : d93634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76036, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76036, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76037 q = 1) (hb : d93635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76037, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76037, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76056 q = 1) (hb : d93656 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76056, d93656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76056, d93656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21655 (p : Pattern) (ha : d76057 p = 1) (hb : d93657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d69120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19018 q ha hb
    | true =>
      simp only [d6957, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d69121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69122 q = 1) (hb : d93637 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d69122, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69122, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69123 q = 1) (hb : d93638 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d69123, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69123, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69124 q = 1) (hb : d93639 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d69124, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69124, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76057 q = 1) (hb : d93657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76057, d93657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76057, d93657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21656 (p : Pattern) (ha : d76065 p = 1) (hb : d93663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76025 q = 1) (hb : d93623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76025, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21648 q ha hb
    | true =>
      simp only [d76025, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q hb ha
  have h2 (q : Pattern) (ha : d76026 q = 1) (hb : d93624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76026, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76026, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76027 q = 1) (hb : d93625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76027, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76027, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76028 q = 1) (hb : d93626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76028, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76028, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76032 q = 1) (hb : d93630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76032, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21649 q ha hb
    | true =>
      simp only [d76032, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q hb ha
  have h6 (q : Pattern) (ha : d76033 q = 1) (hb : d93631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76033, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76033, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76034 q = 1) (hb : d93632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76034, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76034, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d76039 q = 1) (hb : d93641 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76039, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21650 q ha hb
    | true =>
      simp only [d76039, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21647 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76005 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76040 q = 1) (hb : d93642 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76040, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76040, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8809 q = 1) (hb : d76041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19025 q ha hb
    | true =>
      simp only [d8809, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8810 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8810, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76043 q = 1) (hb : d93643 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76043, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76043, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76044 q = 1) (hb : d93644 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76044, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76044, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76045 q = 1) (hb : d93645 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76045, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76045, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76048 q = 1) (hb : d93648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76048, d93648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21652 q ha hb
    | true =>
      simp only [d76048, d93648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro193 q hb ha
  have h17 (q : Pattern) (ha : d76049 q = 1) (hb : d93649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76049, d93649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76049, d93649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76050 q = 1) (hb : d93650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76050, d93650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76050, d93650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d76051 q = 1) (hb : d93651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76051, d93651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76051, d93651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76053 q = 1) (hb : d93653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76053, d93653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21653 q ha hb
    | true =>
      simp only [d76053, d93653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q hb ha
  have h21 (q : Pattern) (ha : d76054 q = 1) (hb : d93654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76054, d93654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76054, d93654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d76055 q = 1) (hb : d93655 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76055, d93655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76055, d93655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d76058 q = 1) (hb : d93658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76058, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21654 q ha hb
    | true =>
      simp only [d76058, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21655 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d76014 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76059 q = 1) (hb : d93659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76059, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76059, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8831 q = 1) (hb : d76060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19031 q ha hb
    | true =>
      simp only [d8831, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8832 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8832, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76062 q = 1) (hb : d93660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76062, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76062, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d76063 q = 1) (hb : d93661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76063, d93661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76063, d93661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76064 q = 1) (hb : d93662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76064, d93662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76064, d93662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76065 q = 1) (hb : d93663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76065, d93663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76065, d93663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21657 (p : Pattern) (ha : d76072 p = 1) (hb : d93670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76067 q = 1) (hb : d93665 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76067, d93665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21647 q ha hb
    | true =>
      simp only [d76067, d93665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d76068 q = 1) (hb : d93666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76068, d93666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76068, d93666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76069 q = 1) (hb : d93667 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76069, d93667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76069, d93667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76070 q = 1) (hb : d93668 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76070, d93668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76070, d93668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76071 q = 1) (hb : d93669 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76071, d93669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76071, d93669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d76072 q = 1) (hb : d93670 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76072, d93670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76072, d93670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro21658 (p : Pattern) (ha : d76079 p = 1) (hb : d93677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76058 q = 1) (hb : d93658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76058, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21654 q ha hb
    | true =>
      simp only [d76058, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21655 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76014 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76059 q = 1) (hb : d93659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76059, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76059, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8831 q = 1) (hb : d76060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19031 q ha hb
    | true =>
      simp only [d8831, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8832 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8832, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76062 q = 1) (hb : d93660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76062, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76062, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76077 q = 1) (hb : d93675 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76077, d93675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76077, d93675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76078 q = 1) (hb : d93676 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76078, d93676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76078, d93676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76079 q = 1) (hb : d93677 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76079, d93677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76079, d93677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21659 (p : Pattern) (ha : d76088 p = 1) (hb : d93686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8859 q = 1) (hb : d52906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8859, d52906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19034 q ha hb
    | true =>
      simp only [d8859, d52906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8860 q = 1) (hb : d52907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8860, d52907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8860, d52907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76085 q = 1) (hb : d93683 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76085, d93683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76085, d93683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76086 q = 1) (hb : d93684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76086, d93684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76086, d93684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76087 q = 1) (hb : d93685 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76087, d93685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76087, d93685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76088 q = 1) (hb : d93686 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76088, d93686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76088, d93686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21660 (p : Pattern) (ha : d76107 p = 1) (hb : d93690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7003 q = 1) (hb : d76102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d76102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19036 q ha hb
    | true =>
      simp only [d7003, d76102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7004 q = 1) (hb : d76103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d76103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d76103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76104 q = 1) (hb : d93687 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76104, d93687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76104, d93687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76105 q = 1) (hb : d93688 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76105, d93688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76105, d93688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76106 q = 1) (hb : d93689 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76106, d93689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76106, d93689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76107 q = 1) (hb : d93690 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76107, d93690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76107, d93690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21661 (p : Pattern) (ha : d76120 p = 1) (hb : d93696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76108 q = 1) (hb : d93691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76108, d93691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21659 q ha hb
    | true =>
      simp only [d76108, d93691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21660 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76113 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76114 q = 1) (hb : d93692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76114, d93692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76114, d93692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8889 q = 1) (hb : d76115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8889, d76115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19039 q ha hb
    | true =>
      simp only [d8889, d76115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8890 q = 1) (hb : d76116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8890, d76116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8890, d76116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76117 q = 1) (hb : d93693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76117, d93693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76117, d93693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76118 q = 1) (hb : d93694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76118, d93694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76118, d93694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76119 q = 1) (hb : d93695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76119, d93695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76119, d93695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76120 q = 1) (hb : d93696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76120, d93696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76120, d93696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21662 (p : Pattern) (ha : d76126 p = 1) (hb : d93702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76011 q = 1) (hb : d93610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76011, d93610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76011, d93610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21645 q ha hb
  have h2 (q : Pattern) (ha : d76012 q = 1) (hb : d93611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76012, d93611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76012, d93611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76020 q = 1) (hb : d93618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76020, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21645 q ha hb
    | true =>
      simp only [d76020, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21646 q ha hb
  have h4 (q : Pattern) (ha : d76021 q = 1) (hb : d93619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76021, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76021, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76022 q = 1) (hb : d93620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76022, d93620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76022, d93620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76066 q = 1) (hb : d93664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76066, d93664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21651 q ha hb
    | true =>
      simp only [d76066, d93664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21656 q ha hb
  have h7 (q : Pattern) (ha : d76073 q = 1) (hb : d93671 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76073, d93671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21657 q ha hb
    | true =>
      simp only [d76073, d93671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q hb ha
  have h8 (q : Pattern) (ha : d76074 q = 1) (hb : d93672 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76074, d93672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76074, d93672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76075 q = 1) (hb : d93673 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76075, d93673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76075, d93673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d76076 q = 1) (hb : d93674 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76076, d93674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76076, d93674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76080 q = 1) (hb : d93678 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76080, d93678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76080, d93678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21658 q ha hb
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
  have h13 (q : Pattern) (ha : d76081 q = 1) (hb : d93679 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76081, d93679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76081, d93679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76082 q = 1) (hb : d93680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76082, d93680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76082, d93680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d76083 q = 1) (hb : d93681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76083, d93681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76083, d93681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d76084 q = 1) (hb : d93682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76084, d93682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76084, d93682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76121 q = 1) (hb : d93697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76121, d93697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76121, d93697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21661 q ha hb
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
  have h19 (q : Pattern) (ha : d76122 q = 1) (hb : d93698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76122, d93698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76122, d93698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d76123 q = 1) (hb : d93699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76123, d93699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76123, d93699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d76124 q = 1) (hb : d93700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76124, d93700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76124, d93700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d76125 q = 1) (hb : d93701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76125, d93701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76125, d93701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d76126 q = 1) (hb : d93702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76126, d93702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76126, d93702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21663 (p : Pattern) (ha : d76132 p = 1) (hb : d93708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76127 q = 1) (hb : d93703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76127, d93703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76127, d93703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21662 q ha hb
  have h2 (q : Pattern) (ha : d76128 q = 1) (hb : d93704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76128, d93704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76128, d93704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76129 q = 1) (hb : d93705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76129, d93705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76129, d93705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76130 q = 1) (hb : d93706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76130, d93706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76130, d93706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76131 q = 1) (hb : d93707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76131, d93707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76131, d93707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76132 q = 1) (hb : d93708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76132, d93708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76132, d93708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21664 (p : Pattern) (ha : d76145 p = 1) (hb : d93717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76140 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76140, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19055 q hb ha
    | true =>
      simp only [d76140, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d76141 q = 1) (hb : d93713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76141, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76141, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76142 q = 1) (hb : d93714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76142, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76142, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76143 q = 1) (hb : d93715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76143, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76143, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76144 q = 1) (hb : d93716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76144, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76144, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76145 q = 1) (hb : d93717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76145, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76145, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21665 (p : Pattern) (ha : d76154 p = 1) (hb : d93725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76140 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76140, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19055 q hb ha
    | true =>
      simp only [d76140, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d76141 q = 1) (hb : d93713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76141, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76141, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76142 q = 1) (hb : d93714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76142, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76142, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76143 q = 1) (hb : d93715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76143, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76143, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76144 q = 1) (hb : d93716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76144, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76144, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76149 q = 1) (hb : d93720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76149, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19061 q hb ha
    | true =>
      simp only [d76149, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h7 (q : Pattern) (ha : d76150 q = 1) (hb : d93721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76150, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76150, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76151 q = 1) (hb : d93722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76151, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76151, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d76152 q = 1) (hb : d93723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76152, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76152, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76153 q = 1) (hb : d93724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76153, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76153, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76154 q = 1) (hb : d93725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76154, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76154, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21666 (p : Pattern) (ha : d69238 p = 1) (hb : d93748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d69233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19048 q ha hb
    | true =>
      simp only [d7037, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d69234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69235 q = 1) (hb : d93745 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d69235, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69235, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69236 q = 1) (hb : d93746 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d69236, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69236, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69237 q = 1) (hb : d93747 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d69237, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69237, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69238 q = 1) (hb : d93748 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d69238, d93748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69238, d93748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21667 (p : Pattern) (ha : d76159 p = 1) (hb : d93730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d76136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d76137 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d76137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d76137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76158 q = 1) (hb : d93729 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76158, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76158, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76159 q = 1) (hb : d93730 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76159, d93730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76159, d93730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21668 (p : Pattern) (ha : d76166 p = 1) (hb : d93737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d76136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d76164 q = 1) (hb : d93735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76164, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76164, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d76165 q = 1) (hb : d93736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76165, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76165, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76166 q = 1) (hb : d93737 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76166, d93737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76166, d93737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21669 (p : Pattern) (ha : d76173 p = 1) (hb : d93744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d53118 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19053 q ha hb
    | true =>
      simp only [d8951, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d53119 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76170 q = 1) (hb : d93741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76170, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76170, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76171 q = 1) (hb : d93742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76171, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76171, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76172 q = 1) (hb : d93743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76172, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76172, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76173 q = 1) (hb : d93744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76173, d93744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76173, d93744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21670 (p : Pattern) (ha : d76181 p = 1) (hb : d93754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76160 q = 1) (hb : d93731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76160, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21667 q ha hb
    | true =>
      simp only [d76160, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q hb ha
  have h2 (q : Pattern) (ha : d76161 q = 1) (hb : d93732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76161, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76161, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76162 q = 1) (hb : d93733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76162, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76162, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76163 q = 1) (hb : d93734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76163, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76163, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76167 q = 1) (hb : d93738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76167, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21668 q ha hb
    | true =>
      simp only [d76167, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q hb ha
  have h6 (q : Pattern) (ha : d76168 q = 1) (hb : d93739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76168, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76168, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76169 q = 1) (hb : d93740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76169, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76169, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d76174 q = 1) (hb : d93749 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76174, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21669 q ha hb
    | true =>
      simp only [d76174, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21666 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76140 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76175 q = 1) (hb : d93750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76175, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76175, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8977 q = 1) (hb : d76176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19055 q ha hb
    | true =>
      simp only [d8977, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8978 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8978, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76178 q = 1) (hb : d93751 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76178, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76178, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76179 q = 1) (hb : d93752 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76179, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76179, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76180 q = 1) (hb : d93753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76180, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76180, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76181 q = 1) (hb : d93754 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76181, d93754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76181, d93754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21671 (p : Pattern) (ha : d76182 p = 1) (hb : d93755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d76136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d76137 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d76137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d76137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76158 q = 1) (hb : d93729 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76158, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76158, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76182 q = 1) (hb : d93755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76182, d93755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76182, d93755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21672 (p : Pattern) (ha : d76187 p = 1) (hb : d93760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19043 q ha hb
    | true =>
      simp only [d8912, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d76136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d76136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d76164 q = 1) (hb : d93735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76164, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76164, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d76165 q = 1) (hb : d93736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76165, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76165, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76187 q = 1) (hb : d93760 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76187, d93760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76187, d93760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21673 (p : Pattern) (ha : d76191 p = 1) (hb : d93764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d53118 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19053 q ha hb
    | true =>
      simp only [d8951, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d53119 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76170 q = 1) (hb : d93741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76170, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76170, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76171 q = 1) (hb : d93742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76171, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76171, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76172 q = 1) (hb : d93743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76172, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76172, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76191 q = 1) (hb : d93764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76191, d93764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76191, d93764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21674 (p : Pattern) (ha : d76192 p = 1) (hb : d93765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d69233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19048 q ha hb
    | true =>
      simp only [d7037, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d69234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69235 q = 1) (hb : d93745 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d69235, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69235, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69236 q = 1) (hb : d93746 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d69236, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69236, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69237 q = 1) (hb : d93747 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d69237, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69237, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76192 q = 1) (hb : d93765 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76192, d93765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76192, d93765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21675 (p : Pattern) (ha : d76200 p = 1) (hb : d93771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76160 q = 1) (hb : d93731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76160, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21667 q ha hb
    | true =>
      simp only [d76160, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q hb ha
  have h2 (q : Pattern) (ha : d76161 q = 1) (hb : d93732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76161, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76161, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76162 q = 1) (hb : d93733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76162, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76162, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76163 q = 1) (hb : d93734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76163, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76163, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76167 q = 1) (hb : d93738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76167, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21668 q ha hb
    | true =>
      simp only [d76167, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q hb ha
  have h6 (q : Pattern) (ha : d76168 q = 1) (hb : d93739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76168, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76168, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76169 q = 1) (hb : d93740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76169, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76169, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d76174 q = 1) (hb : d93749 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76174, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21669 q ha hb
    | true =>
      simp only [d76174, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21666 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76140 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76175 q = 1) (hb : d93750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76175, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76175, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8977 q = 1) (hb : d76176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19055 q ha hb
    | true =>
      simp only [d8977, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8978 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8978, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76178 q = 1) (hb : d93751 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76178, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76178, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76179 q = 1) (hb : d93752 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76179, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76179, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76180 q = 1) (hb : d93753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76180, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76180, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76183 q = 1) (hb : d93756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76183, d93756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21671 q ha hb
    | true =>
      simp only [d76183, d93756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro249 q hb ha
  have h17 (q : Pattern) (ha : d76184 q = 1) (hb : d93757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76184, d93757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76184, d93757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76185 q = 1) (hb : d93758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76185, d93758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76185, d93758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d76186 q = 1) (hb : d93759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76186, d93759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76186, d93759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76188 q = 1) (hb : d93761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76188, d93761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21672 q ha hb
    | true =>
      simp only [d76188, d93761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q hb ha
  have h21 (q : Pattern) (ha : d76189 q = 1) (hb : d93762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76189, d93762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76189, d93762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d76190 q = 1) (hb : d93763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76190, d93763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76190, d93763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d76193 q = 1) (hb : d93766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76193, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21673 q ha hb
    | true =>
      simp only [d76193, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21674 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d76149 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76194 q = 1) (hb : d93767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76194, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76194, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8999 q = 1) (hb : d76195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19061 q ha hb
    | true =>
      simp only [d8999, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d9000 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9000, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76197 q = 1) (hb : d93768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76197, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76197, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d76198 q = 1) (hb : d93769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76198, d93769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76198, d93769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76199 q = 1) (hb : d93770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76199, d93770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76199, d93770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76200 q = 1) (hb : d93771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76200, d93771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76200, d93771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21676 (p : Pattern) (ha : d76207 p = 1) (hb : d93778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76202 q = 1) (hb : d93773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76202, d93773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21666 q ha hb
    | true =>
      simp only [d76202, d93773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d76203 q = 1) (hb : d93774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76203, d93774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76203, d93774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76204 q = 1) (hb : d93775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76204, d93775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76204, d93775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76205 q = 1) (hb : d93776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76205, d93776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76205, d93776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76206 q = 1) (hb : d93777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76206, d93777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76206, d93777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d76207 q = 1) (hb : d93778 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76207, d93778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76207, d93778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro21677 (p : Pattern) (ha : d76214 p = 1) (hb : d93785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76193 q = 1) (hb : d93766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76193, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21673 q ha hb
    | true =>
      simp only [d76193, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21674 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76194 q = 1) (hb : d93767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76194, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76194, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8999 q = 1) (hb : d76195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19061 q ha hb
    | true =>
      simp only [d8999, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9000 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9000, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76197 q = 1) (hb : d93768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76197, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76197, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76212 q = 1) (hb : d93783 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76212, d93783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76212, d93783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76213 q = 1) (hb : d93784 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76213, d93784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76213, d93784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76214 q = 1) (hb : d93785 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76214, d93785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76214, d93785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21678 (p : Pattern) (ha : d76223 p = 1) (hb : d93794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9027 q = 1) (hb : d53221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9027, d53221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19064 q ha hb
    | true =>
      simp only [d9027, d53221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9028 q = 1) (hb : d53222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9028, d53222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9028, d53222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76220 q = 1) (hb : d93791 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76220, d93791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76220, d93791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76221 q = 1) (hb : d93792 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76221, d93792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76221, d93792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76222 q = 1) (hb : d93793 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76222, d93793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76222, d93793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76223 q = 1) (hb : d93794 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76223, d93794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76223, d93794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21679 (p : Pattern) (ha : d76242 p = 1) (hb : d93798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7083 q = 1) (hb : d76237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d76237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19066 q ha hb
    | true =>
      simp only [d7083, d76237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7084 q = 1) (hb : d76238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d76238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d76238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76239 q = 1) (hb : d93795 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76239, d93795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76239, d93795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76240 q = 1) (hb : d93796 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76240, d93796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76240, d93796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76241 q = 1) (hb : d93797 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76241, d93797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76241, d93797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76242 q = 1) (hb : d93798 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76242, d93798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76242, d93798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21680 (p : Pattern) (ha : d76255 p = 1) (hb : d93804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76243 q = 1) (hb : d93799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76243, d93799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21678 q ha hb
    | true =>
      simp only [d76243, d93799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21679 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76248 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76249 q = 1) (hb : d93800 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76249, d93800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76249, d93800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9057 q = 1) (hb : d76250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9057, d76250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19069 q ha hb
    | true =>
      simp only [d9057, d76250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9058 q = 1) (hb : d76251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9058, d76251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9058, d76251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76252 q = 1) (hb : d93801 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76252, d93801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76252, d93801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76253 q = 1) (hb : d93802 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76253, d93802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76253, d93802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76254 q = 1) (hb : d93803 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76254, d93803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76254, d93803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76255 q = 1) (hb : d93804 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76255, d93804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76255, d93804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21681 (p : Pattern) (ha : d76261 p = 1) (hb : d93810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76146 q = 1) (hb : d93718 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76146, d93718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76146, d93718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21664 q ha hb
  have h2 (q : Pattern) (ha : d76147 q = 1) (hb : d93719 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76147, d93719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76147, d93719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76155 q = 1) (hb : d93726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76155, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21664 q ha hb
    | true =>
      simp only [d76155, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21665 q ha hb
  have h4 (q : Pattern) (ha : d76156 q = 1) (hb : d93727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76156, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76156, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76157 q = 1) (hb : d93728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76157, d93728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76157, d93728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76201 q = 1) (hb : d93772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76201, d93772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21670 q ha hb
    | true =>
      simp only [d76201, d93772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21675 q ha hb
  have h7 (q : Pattern) (ha : d76208 q = 1) (hb : d93779 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76208, d93779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21676 q ha hb
    | true =>
      simp only [d76208, d93779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q hb ha
  have h8 (q : Pattern) (ha : d76209 q = 1) (hb : d93780 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76209, d93780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76209, d93780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76210 q = 1) (hb : d93781 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76210, d93781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76210, d93781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d76211 q = 1) (hb : d93782 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76211, d93782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76211, d93782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76215 q = 1) (hb : d93786 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76215, d93786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76215, d93786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21677 q ha hb
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
  have h13 (q : Pattern) (ha : d76216 q = 1) (hb : d93787 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76216, d93787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76216, d93787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76217 q = 1) (hb : d93788 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76217, d93788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76217, d93788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d76218 q = 1) (hb : d93789 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76218, d93789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76218, d93789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d76219 q = 1) (hb : d93790 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76219, d93790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76219, d93790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76256 q = 1) (hb : d93805 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76256, d93805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76256, d93805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21680 q ha hb
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
  have h19 (q : Pattern) (ha : d76257 q = 1) (hb : d93806 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76257, d93806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76257, d93806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d76258 q = 1) (hb : d93807 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76258, d93807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76258, d93807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d76259 q = 1) (hb : d93808 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76259, d93808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76259, d93808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d76260 q = 1) (hb : d93809 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76260, d93809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76260, d93809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d76261 q = 1) (hb : d93810 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76261, d93810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76261, d93810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21682 (p : Pattern) (ha : d76267 p = 1) (hb : d93816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76262 q = 1) (hb : d93811 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76262, d93811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76262, d93811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21681 q ha hb
  have h2 (q : Pattern) (ha : d76263 q = 1) (hb : d93812 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76263, d93812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76263, d93812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76264 q = 1) (hb : d93813 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76264, d93813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76264, d93813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76265 q = 1) (hb : d93814 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76265, d93814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76265, d93814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76266 q = 1) (hb : d93815 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76266, d93815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76266, d93815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76267 q = 1) (hb : d93816 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76267, d93816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76267, d93816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21683 (p : Pattern) (ha : d76281 p = 1) (hb : d93826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76276 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76276, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19085 q hb ha
    | true =>
      simp only [d76276, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d76277 q = 1) (hb : d93822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76277, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76277, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76278 q = 1) (hb : d93823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76278, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76278, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76279 q = 1) (hb : d93824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76279, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76279, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76280 q = 1) (hb : d93825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76280, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76280, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76281 q = 1) (hb : d93826 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76281, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76281, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21684 (p : Pattern) (ha : d76290 p = 1) (hb : d93834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76276 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76276, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19085 q hb ha
    | true =>
      simp only [d76276, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d76277 q = 1) (hb : d93822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76277, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76277, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76278 q = 1) (hb : d93823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76278, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76278, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76279 q = 1) (hb : d93824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76279, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76279, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76280 q = 1) (hb : d93825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76280, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76280, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76285 q = 1) (hb : d93829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76285, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19091 q hb ha
    | true =>
      simp only [d76285, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h7 (q : Pattern) (ha : d76286 q = 1) (hb : d93830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76286, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76286, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76287 q = 1) (hb : d93831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76287, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76287, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d76288 q = 1) (hb : d93832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76288, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76288, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76289 q = 1) (hb : d93833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76289, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76289, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76290 q = 1) (hb : d93834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76290, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76290, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21685 (p : Pattern) (ha : d69348 p = 1) (hb : d93857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d69343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19078 q ha hb
    | true =>
      simp only [d7118, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69345 q = 1) (hb : d93854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d69345, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69345, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69346 q = 1) (hb : d93855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d69346, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69346, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69347 q = 1) (hb : d93856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d69347, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69347, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69348 q = 1) (hb : d93857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d69348, d93857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69348, d93857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21686 (p : Pattern) (ha : d76295 p = 1) (hb : d93839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d76272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d76273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d76273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d76273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76294 q = 1) (hb : d93838 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76294, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76294, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76295 q = 1) (hb : d93839 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76295, d93839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76295, d93839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21687 (p : Pattern) (ha : d76302 p = 1) (hb : d93846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d76272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d76300 q = 1) (hb : d93844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76300, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76300, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d76301 q = 1) (hb : d93845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76301, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76301, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76302 q = 1) (hb : d93846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76302, d93846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76302, d93846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21688 (p : Pattern) (ha : d76309 p = 1) (hb : d93853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19083 q ha hb
    | true =>
      simp only [d9120, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76306 q = 1) (hb : d93850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76306, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76306, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76307 q = 1) (hb : d93851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76307, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76307, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76308 q = 1) (hb : d93852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76308, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76308, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76309 q = 1) (hb : d93853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76309, d93853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76309, d93853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21689 (p : Pattern) (ha : d76317 p = 1) (hb : d93863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76296 q = 1) (hb : d93840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76296, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21686 q ha hb
    | true =>
      simp only [d76296, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q hb ha
  have h2 (q : Pattern) (ha : d76297 q = 1) (hb : d93841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76297, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76297, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76298 q = 1) (hb : d93842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76298, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76298, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76299 q = 1) (hb : d93843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76299, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76299, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76303 q = 1) (hb : d93847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76303, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21687 q ha hb
    | true =>
      simp only [d76303, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q hb ha
  have h6 (q : Pattern) (ha : d76304 q = 1) (hb : d93848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76304, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76304, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76305 q = 1) (hb : d93849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76305, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76305, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d76310 q = 1) (hb : d93858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76310, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21688 q ha hb
    | true =>
      simp only [d76310, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21685 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76276 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76311 q = 1) (hb : d93859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76311, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76311, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9146 q = 1) (hb : d76312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19085 q ha hb
    | true =>
      simp only [d9146, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9147 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9147, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76314 q = 1) (hb : d93860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76314, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76314, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76315 q = 1) (hb : d93861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76315, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76315, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76316 q = 1) (hb : d93862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76316, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76316, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76317 q = 1) (hb : d93863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76317, d93863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76317, d93863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro21690 (p : Pattern) (ha : d76318 p = 1) (hb : d93864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d76272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d76273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d76273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d76273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76294 q = 1) (hb : d93838 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76294, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76294, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76318 q = 1) (hb : d93864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76318, d93864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76318, d93864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21691 (p : Pattern) (ha : d76323 p = 1) (hb : d93869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19073 q ha hb
    | true =>
      simp only [d9081, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d76272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d76272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d76300 q = 1) (hb : d93844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76300, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76300, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d76301 q = 1) (hb : d93845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76301, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76301, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76323 q = 1) (hb : d93869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76323, d93869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76323, d93869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21692 (p : Pattern) (ha : d76327 p = 1) (hb : d93873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19083 q ha hb
    | true =>
      simp only [d9120, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76306 q = 1) (hb : d93850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76306, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76306, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76307 q = 1) (hb : d93851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76307, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76307, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76308 q = 1) (hb : d93852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76308, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76308, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76327 q = 1) (hb : d93873 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76327, d93873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76327, d93873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21693 (p : Pattern) (ha : d76328 p = 1) (hb : d93874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d69343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19078 q ha hb
    | true =>
      simp only [d7118, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69345 q = 1) (hb : d93854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d69345, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69345, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69346 q = 1) (hb : d93855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d69346, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69346, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69347 q = 1) (hb : d93856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d69347, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69347, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76328 q = 1) (hb : d93874 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76328, d93874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76328, d93874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21694 (p : Pattern) (ha : d76336 p = 1) (hb : d93880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76296 q = 1) (hb : d93840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76296, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21686 q ha hb
    | true =>
      simp only [d76296, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q hb ha
  have h2 (q : Pattern) (ha : d76297 q = 1) (hb : d93841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76297, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76297, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76298 q = 1) (hb : d93842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76298, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76298, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76299 q = 1) (hb : d93843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76299, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76299, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76303 q = 1) (hb : d93847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76303, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21687 q ha hb
    | true =>
      simp only [d76303, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q hb ha
  have h6 (q : Pattern) (ha : d76304 q = 1) (hb : d93848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76304, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76304, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76305 q = 1) (hb : d93849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76305, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76305, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d76310 q = 1) (hb : d93858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76310, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21688 q ha hb
    | true =>
      simp only [d76310, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21685 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76276 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76311 q = 1) (hb : d93859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76311, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76311, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9146 q = 1) (hb : d76312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19085 q ha hb
    | true =>
      simp only [d9146, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9147 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9147, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76314 q = 1) (hb : d93860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76314, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76314, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76315 q = 1) (hb : d93861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76315, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76315, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76316 q = 1) (hb : d93862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76316, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76316, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76319 q = 1) (hb : d93865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76319, d93865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21690 q ha hb
    | true =>
      simp only [d76319, d93865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro308 q hb ha
  have h17 (q : Pattern) (ha : d76320 q = 1) (hb : d93866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76320, d93866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76320, d93866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76321 q = 1) (hb : d93867 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76321, d93867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76321, d93867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d76322 q = 1) (hb : d93868 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76322, d93868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76322, d93868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76324 q = 1) (hb : d93870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76324, d93870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21691 q ha hb
    | true =>
      simp only [d76324, d93870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q hb ha
  have h21 (q : Pattern) (ha : d76325 q = 1) (hb : d93871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76325, d93871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76325, d93871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d76326 q = 1) (hb : d93872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76326, d93872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76326, d93872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d76329 q = 1) (hb : d93875 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76329, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21692 q ha hb
    | true =>
      simp only [d76329, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21693 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d76285 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76330 q = 1) (hb : d93876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76330, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76330, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d9168 q = 1) (hb : d76331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19091 q ha hb
    | true =>
      simp only [d9168, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d9169 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9169, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76333 q = 1) (hb : d93877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76333, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76333, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d76334 q = 1) (hb : d93878 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76334, d93878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76334, d93878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76335 q = 1) (hb : d93879 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76335, d93879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76335, d93879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76336 q = 1) (hb : d93880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76336, d93880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76336, d93880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro21695 (p : Pattern) (ha : d76343 p = 1) (hb : d93887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76338 q = 1) (hb : d93882 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76338, d93882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21685 q ha hb
    | true =>
      simp only [d76338, d93882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d76339 q = 1) (hb : d93883 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76339, d93883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76339, d93883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76340 q = 1) (hb : d93884 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76340, d93884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76340, d93884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76341 q = 1) (hb : d93885 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76341, d93885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76341, d93885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76342 q = 1) (hb : d93886 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76342, d93886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76342, d93886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d76343 q = 1) (hb : d93887 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76343, d93887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76343, d93887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro21696 (p : Pattern) (ha : d76350 p = 1) (hb : d93894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76329 q = 1) (hb : d93875 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76329, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21692 q ha hb
    | true =>
      simp only [d76329, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21693 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76330 q = 1) (hb : d93876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76330, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76330, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9168 q = 1) (hb : d76331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19091 q ha hb
    | true =>
      simp only [d9168, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9169 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9169, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76333 q = 1) (hb : d93877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76333, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76333, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76348 q = 1) (hb : d93892 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76348, d93892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76348, d93892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76349 q = 1) (hb : d93893 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76349, d93893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76349, d93893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76350 q = 1) (hb : d93894 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76350, d93894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76350, d93894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21697 (p : Pattern) (ha : d76359 p = 1) (hb : d93903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9196 q = 1) (hb : d53538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9196, d53538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19094 q ha hb
    | true =>
      simp only [d9196, d53538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9197 q = 1) (hb : d53539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9197, d53539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9197, d53539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76356 q = 1) (hb : d93900 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76356, d93900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76356, d93900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76357 q = 1) (hb : d93901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76357, d93901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76357, d93901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76358 q = 1) (hb : d93902 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76358, d93902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76358, d93902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76359 q = 1) (hb : d93903 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76359, d93903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76359, d93903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21698 (p : Pattern) (ha : d76378 p = 1) (hb : d93907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7164 q = 1) (hb : d76373 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d76373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19096 q ha hb
    | true =>
      simp only [d7164, d76373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7165 q = 1) (hb : d76374 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d76374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d76374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76375 q = 1) (hb : d93904 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d76375, d93904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76375, d93904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76376 q = 1) (hb : d93905 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d76376, d93905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76376, d93905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76377 q = 1) (hb : d93906 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d76377, d93906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76377, d93906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76378 q = 1) (hb : d93907 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d76378, d93907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76378, d93907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21699 (p : Pattern) (ha : d76391 p = 1) (hb : d93913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76379 q = 1) (hb : d93908 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76379, d93908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21697 q ha hb
    | true =>
      simp only [d76379, d93908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21698 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76384 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76385 q = 1) (hb : d93909 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76385, d93909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76385, d93909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9226 q = 1) (hb : d76386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9226, d76386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19099 q ha hb
    | true =>
      simp only [d9226, d76386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9227 q = 1) (hb : d76387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9227, d76387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9227, d76387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76388 q = 1) (hb : d93910 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76388, d93910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76388, d93910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76389 q = 1) (hb : d93911 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76389, d93911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76389, d93911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76390 q = 1) (hb : d93912 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76390, d93912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76390, d93912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76391 q = 1) (hb : d93913 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76391, d93913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76391, d93913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro21700 (p : Pattern) (ha : d76397 p = 1) (hb : d93919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76282 q = 1) (hb : d93827 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76282, d93827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76282, d93827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21683 q ha hb
  have h2 (q : Pattern) (ha : d76283 q = 1) (hb : d93828 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76283, d93828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76283, d93828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76291 q = 1) (hb : d93835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76291, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21683 q ha hb
    | true =>
      simp only [d76291, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21684 q ha hb
  have h4 (q : Pattern) (ha : d76292 q = 1) (hb : d93836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76292, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76292, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76293 q = 1) (hb : d93837 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76293, d93837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76293, d93837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76337 q = 1) (hb : d93881 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76337, d93881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21689 q ha hb
    | true =>
      simp only [d76337, d93881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21694 q ha hb
  have h7 (q : Pattern) (ha : d76344 q = 1) (hb : d93888 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76344, d93888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21695 q ha hb
    | true =>
      simp only [d76344, d93888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q hb ha
  have h8 (q : Pattern) (ha : d76345 q = 1) (hb : d93889 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76345, d93889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76345, d93889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76346 q = 1) (hb : d93890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76346, d93890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76346, d93890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d76347 q = 1) (hb : d93891 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76347, d93891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76347, d93891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76351 q = 1) (hb : d93895 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76351, d93895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76351, d93895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21696 q ha hb
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
  have h13 (q : Pattern) (ha : d76352 q = 1) (hb : d93896 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76352, d93896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76352, d93896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76353 q = 1) (hb : d93897 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76353, d93897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76353, d93897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d76354 q = 1) (hb : d93898 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76354, d93898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76354, d93898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d76355 q = 1) (hb : d93899 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76355, d93899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76355, d93899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76392 q = 1) (hb : d93914 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76392, d93914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76392, d93914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21699 q ha hb
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
  have h19 (q : Pattern) (ha : d76393 q = 1) (hb : d93915 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76393, d93915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76393, d93915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d76394 q = 1) (hb : d93916 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76394, d93916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76394, d93916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d76395 q = 1) (hb : d93917 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76395, d93917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76395, d93917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d76396 q = 1) (hb : d93918 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76396, d93918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76396, d93918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d76397 q = 1) (hb : d93919 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76397, d93919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76397, d93919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21701 (p : Pattern) (ha : d76403 p = 1) (hb : d93925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76398 q = 1) (hb : d93920 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76398, d93920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76398, d93920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21700 q ha hb
  have h2 (q : Pattern) (ha : d76399 q = 1) (hb : d93921 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76399, d93921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76399, d93921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76400 q = 1) (hb : d93922 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76400, d93922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76400, d93922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76401 q = 1) (hb : d93923 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76401, d93923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76401, d93923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76402 q = 1) (hb : d93924 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76402, d93924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76402, d93924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76403 q = 1) (hb : d93925 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76403, d93925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76403, d93925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21702 (p : Pattern) (ha : d76409 p = 1) (hb : d93931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d75872 q = 1) (hb : d93496 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d75872, d93496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21606 q ha hb
    | true =>
      simp only [d75872, d93496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21625 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75999 q = 1) (hb : d93602 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d75999, d93602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75999, d93602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21644 q ha hb
  have h3 (q : Pattern) (ha : d76000 q = 1) (hb : d93603 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76000, d93603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76000, d93603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76133 q = 1) (hb : d93709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76133, d93709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76133, d93709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21663 q ha hb
  have h5 (q : Pattern) (ha : d76134 q = 1) (hb : d93710 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76134, d93710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76134, d93710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76135 q = 1) (hb : d93711 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76135, d93711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76135, d93711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76268 q = 1) (hb : d93817 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76268, d93817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76268, d93817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21682 q ha hb
  have h8 (q : Pattern) (ha : d76269 q = 1) (hb : d93818 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76269, d93818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76269, d93818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76270 q = 1) (hb : d93819 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76270, d93819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76270, d93819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76271 q = 1) (hb : d93820 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d76271, d93820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76271, d93820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76404 q = 1) (hb : d93926 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76404, d93926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76404, d93926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21701 q ha hb
  have h12 (q : Pattern) (ha : d76405 q = 1) (hb : d93927 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76405, d93927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76405, d93927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76406 q = 1) (hb : d93928 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76406, d93928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76406, d93928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76407 q = 1) (hb : d93929 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d76407, d93929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76407, d93929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76408 q = 1) (hb : d93930 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d76408, d93930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76408, d93930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76409 q = 1) (hb : d93931 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d76409, d93931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76409, d93931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro21703 (p : Pattern) (ha : d76415 p = 1) (hb : d93937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76410 q = 1) (hb : d93932 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d76410, d93932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21702 q ha hb
    | true =>
      simp only [d76410, d93932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76411 q = 1) (hb : d93933 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d76411, d93933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76411, d93933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76412 q = 1) (hb : d93934 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d76412, d93934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76412, d93934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76413 q = 1) (hb : d93935 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d76413, d93935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76413, d93935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76414 q = 1) (hb : d93936 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d76414, d93936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76414, d93936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76415 q = 1) (hb : d93937 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d76415, d93937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76415, d93937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21704 (p : Pattern) (ha : d76421 p = 1) (hb : d93943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76416 q = 1) (hb : d93938 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d76416, d93938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21703 q ha hb
    | true =>
      simp only [d76416, d93938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76417 q = 1) (hb : d93939 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d76417, d93939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76417, d93939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76418 q = 1) (hb : d93940 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d76418, d93940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76418, d93940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76419 q = 1) (hb : d93941 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d76419, d93941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76419, d93941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76420 q = 1) (hb : d93942 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d76420, d93942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76420, d93942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76421 q = 1) (hb : d93943 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d76421, d93943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76421, d93943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21705 (p : Pattern) (ha : d76427 p = 1) (hb : d93949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76422 q = 1) (hb : d93944 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d76422, d93944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21704 q ha hb
    | true =>
      simp only [d76422, d93944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76423 q = 1) (hb : d93945 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d76423, d93945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76423, d93945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76424 q = 1) (hb : d93946 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d76424, d93946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76424, d93946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76425 q = 1) (hb : d93947 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d76425, d93947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76425, d93947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76426 q = 1) (hb : d93948 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d76426, d93948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76426, d93948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76427 q = 1) (hb : d93949 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d76427, d93949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76427, d93949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21706 (p : Pattern) (ha : d76433 p = 1) (hb : d93955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76428 q = 1) (hb : d93950 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d76428, d93950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21705 q ha hb
    | true =>
      simp only [d76428, d93950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76429 q = 1) (hb : d93951 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d76429, d93951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76429, d93951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76430 q = 1) (hb : d93952 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d76430, d93952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76430, d93952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76431 q = 1) (hb : d93953 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d76431, d93953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76431, d93953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76432 q = 1) (hb : d93954 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d76432, d93954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76432, d93954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76433 q = 1) (hb : d93955 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d76433, d93955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76433, d93955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21707 (p : Pattern) (ha : d76439 p = 1) (hb : d93961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76434 q = 1) (hb : d93956 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d76434, d93956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21706 q ha hb
    | true =>
      simp only [d76434, d93956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76435 q = 1) (hb : d93957 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d76435, d93957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76435, d93957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76436 q = 1) (hb : d93958 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d76436, d93958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76436, d93958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76437 q = 1) (hb : d93959 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d76437, d93959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76437, d93959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76438 q = 1) (hb : d93960 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d76438, d93960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76438, d93960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76439 q = 1) (hb : d93961 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d76439, d93961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76439, d93961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21708 (p : Pattern) (ha : d76445 p = 1) (hb : d93967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76440 q = 1) (hb : d93962 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d76440, d93962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21707 q ha hb
    | true =>
      simp only [d76440, d93962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76441 q = 1) (hb : d93963 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d76441, d93963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76441, d93963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76442 q = 1) (hb : d93964 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d76442, d93964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76442, d93964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76443 q = 1) (hb : d93965 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d76443, d93965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76443, d93965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76444 q = 1) (hb : d93966 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d76444, d93966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76444, d93966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76445 q = 1) (hb : d93967 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d76445, d93967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76445, d93967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21709 (p : Pattern) (ha : d76451 p = 1) (hb : d93973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76446 q = 1) (hb : d93968 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d76446, d93968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21708 q ha hb
    | true =>
      simp only [d76446, d93968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76447 q = 1) (hb : d93969 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d76447, d93969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76447, d93969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76448 q = 1) (hb : d93970 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d76448, d93970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76448, d93970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76449 q = 1) (hb : d93971 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d76449, d93971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76449, d93971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76450 q = 1) (hb : d93972 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d76450, d93972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76450, d93972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76451 q = 1) (hb : d93973 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d76451, d93973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76451, d93973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21710 (p : Pattern) (ha : d92314 p = 1) (hb : d94521 p = 1) : d93976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d92314 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8246 q = 1) (hb : d92314 q = 1) : d93276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21451 q ha hb
    | true =>
      simp only [d8246, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8292 q = 1) (hb : d92314 q = 1) : d93318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8293 q = 1) (hb : d92314 q = 1) : d93319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8293, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8294 q = 1) (hb : d92314 q = 1) : d93320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8295 q = 1) (hb : d92314 q = 1) : d93321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94521 q = 1) : d93976 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94521, d93976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94521, d93976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro21711 (p : Pattern) (ha : d92314 p = 1) (hb : d94531 p = 1) : d93986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d92314 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8268 q = 1) (hb : d92314 q = 1) : d93294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21454 q ha hb
    | true =>
      simp only [d8268, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94527 q = 1) : d93982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94527, d93982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94527, d93982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94528 q = 1) : d93983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94528, d93983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94528, d93983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94529 q = 1) : d93984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94529, d93984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94529, d93984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94530 q = 1) : d93985 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94530, d93985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94530, d93985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94531 q = 1) : d93986 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94531, d93986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94531, d93986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21712 (p : Pattern) (ha : d92314 p = 1) (hb : d94537 p = 1) : d93992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8297 q = 1) (hb : d92314 q = 1) : d93323 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21457 q ha hb
    | true =>
      simp only [d8297, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21458 q ha hb
  have h2 (q : Pattern) (ha : d8298 q = 1) (hb : d92314 q = 1) : d93324 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8298, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94519 q = 1) : d93974 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94519, d93974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94519, d93974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94520 q = 1) : d93975 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94520, d93975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94520, d93975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94522 q = 1) : d93977 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94522, d93977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94522, d93977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21710 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94523 q = 1) : d93978 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94523, d93978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94523, d93978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94524 q = 1) : d93979 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94524, d93979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94524, d93979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94525 q = 1) : d93980 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94525, d93980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94525, d93980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94526 q = 1) : d93981 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94526, d93981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94526, d93981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94532 q = 1) : d93987 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94532, d93987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94532, d93987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21711 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94533 q = 1) : d93988 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94533, d93988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94533, d93988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94534 q = 1) : d93989 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94534, d93989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94534, d93989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94535 q = 1) : d93990 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94535, d93990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94535, d93990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94536 q = 1) : d93991 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94536, d93991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94536, d93991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94537 q = 1) : d93992 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94537, d93992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94537, d93992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21713 (p : Pattern) (ha : d92314 p = 1) (hb : d94543 p = 1) : d93998 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d92314 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94538 q = 1) : d93993 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94538, d93993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94538, d93993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21712 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94539 q = 1) : d93994 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94539, d93994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94539, d93994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94540 q = 1) : d93995 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94540, d93995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94540, d93995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94541 q = 1) : d93996 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94541, d93996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94541, d93996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94542 q = 1) : d93997 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94542, d93997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94542, d93997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94543 q = 1) : d93998 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94543, d93998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94543, d93998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21714 (p : Pattern) (ha : d92314 p = 1) (hb : d94546 p = 1) : d94001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d501 q = 1) (hb : d92314 q = 1) : d501 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8430 q = 1) (hb : d92314 q = 1) : d93399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21475 q ha hb
    | true =>
      simp only [d8430, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8431 q = 1) (hb : d92314 q = 1) : d93400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8432 q = 1) (hb : d92314 q = 1) : d93401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8432, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8433 q = 1) (hb : d92314 q = 1) : d93402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8434 q = 1) (hb : d92314 q = 1) : d93403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94546 q = 1) : d94001 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94546, d94001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94546, d94001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro21715 (p : Pattern) (ha : d92314 p = 1) (hb : d94555 p = 1) : d8555 p = 1 := by
  have h0 (q : Pattern) (ha : d8379 q = 1) (hb : d92313 q = 1) : d8379 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d685 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94552 q = 1) : d8552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92314, d94552, d8552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92314, d94552, d8552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94553 q = 1) : d8553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94553, d8553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94553, d8553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94554 q = 1) : d8554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94554, d8554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94554, d8554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94555 q = 1) : d8555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94555, d8555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94555, d8555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h6 p ha hb
theorem andIntro21716 (p : Pattern) (ha : d92314 p = 1) (hb : d94561 p = 1) : d94012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d730 q = 1) (hb : d92314 q = 1) : d730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94556 q = 1) : d94007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94556, d94007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21715 q ha hb
    | true =>
      simp only [d94556, d94007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94557 q = 1) : d94008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94557, d94008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94557, d94008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94558 q = 1) : d94009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94558, d94009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94558, d94009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94559 q = 1) : d94010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94559, d94010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94559, d94010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94560 q = 1) : d94011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94560, d94011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94560, d94011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94561 q = 1) : d94012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94561, d94012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94561, d94012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21717 (p : Pattern) (ha : d92314 p = 1) (hb : d94567 p = 1) : d94018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8436 q = 1) (hb : d92314 q = 1) : d93405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21474 q ha hb
    | true =>
      simp only [d8436, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21476 q ha hb
  have h2 (q : Pattern) (ha : d8437 q = 1) (hb : d92314 q = 1) : d93406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8437, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94544 q = 1) : d93999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94544, d93999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94544, d93999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94545 q = 1) : d94000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94545, d94000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94545, d94000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94547 q = 1) : d94002 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94547, d94002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94547, d94002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21714 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94548 q = 1) : d94003 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94548, d94003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94548, d94003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94549 q = 1) : d94004 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94549, d94004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94549, d94004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94550 q = 1) : d94005 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94550, d94005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94550, d94005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94551 q = 1) : d94006 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94551, d94006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94551, d94006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94562 q = 1) : d94013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94562, d94013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94562, d94013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21716 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94563 q = 1) : d94014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94563, d94014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94563, d94014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94564 q = 1) : d94015 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94564, d94015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94564, d94015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94565 q = 1) : d94016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94565, d94016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94565, d94016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94566 q = 1) : d94017 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94566, d94017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94566, d94017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94567 q = 1) : d94018 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94567, d94018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94567, d94018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21718 (p : Pattern) (ha : d92314 p = 1) (hb : d94573 p = 1) : d94024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94568 q = 1) : d94019 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94568, d94019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94568, d94019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21717 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94569 q = 1) : d94020 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94569, d94020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94569, d94020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94570 q = 1) : d94021 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94570, d94021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94570, d94021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94571 q = 1) : d94022 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94571, d94022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94571, d94022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94572 q = 1) : d94023 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94572, d94023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94572, d94023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94573 q = 1) : d94024 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94573, d94024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94573, d94024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21719 (p : Pattern) (ha : d92314 p = 1) (hb : d94577 p = 1) : d94028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d793 q = 1) (hb : d92314 q = 1) : d793 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8592 q = 1) (hb : d92314 q = 1) : d93505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21496 q ha hb
    | true =>
      simp only [d8592, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8593 q = 1) (hb : d92314 q = 1) : d93506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8594 q = 1) (hb : d92314 q = 1) : d93507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8594, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8595 q = 1) (hb : d92314 q = 1) : d93508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8596 q = 1) (hb : d92314 q = 1) : d93509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94577 q = 1) : d94028 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94577, d94028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94577, d94028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro21720 (p : Pattern) (ha : d92314 p = 1) (hb : d94586 p = 1) : d8721 p = 1 := by
  have h0 (q : Pattern) (ha : d8717 q = 1) (hb : d92313 q = 1) : d8717 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94583 q = 1) : d8718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92314, d94583, d8718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92314, d94583, d8718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94584 q = 1) : d8719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94584, d8719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94584, d8719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94585 q = 1) : d8720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94585, d8720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94585, d8720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94586 q = 1) : d8721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94586, d8721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94586, d8721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h6 p ha hb
theorem andIntro21721 (p : Pattern) (ha : d92314 p = 1) (hb : d94592 p = 1) : d94039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1063 q = 1) (hb : d92314 q = 1) : d1063 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94587 q = 1) : d94034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94587, d94034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21720 q ha hb
    | true =>
      simp only [d94587, d94034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94588 q = 1) : d94035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94588, d94035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94588, d94035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94589 q = 1) : d94036 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94589, d94036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94589, d94036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94590 q = 1) : d94037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94590, d94037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94590, d94037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94591 q = 1) : d94038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94591, d94038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94591, d94038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94592 q = 1) : d94039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94592, d94039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94592, d94039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21722 (p : Pattern) (ha : d92314 p = 1) (hb : d94598 p = 1) : d94045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8598 q = 1) (hb : d92314 q = 1) : d93511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21495 q ha hb
    | true =>
      simp only [d8598, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21497 q ha hb
  have h2 (q : Pattern) (ha : d8599 q = 1) (hb : d92314 q = 1) : d93512 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8599, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94575 q = 1) : d94026 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94575, d94026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94575, d94026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94576 q = 1) : d94027 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94576, d94027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94576, d94027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94578 q = 1) : d94029 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94578, d94029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94578, d94029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21719 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94579 q = 1) : d94030 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94579, d94030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94579, d94030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94580 q = 1) : d94031 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94580, d94031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94580, d94031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94581 q = 1) : d94032 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94581, d94032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94581, d94032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94582 q = 1) : d94033 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94582, d94033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94582, d94033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94593 q = 1) : d94040 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94593, d94040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94593, d94040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21721 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94594 q = 1) : d94041 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94594, d94041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94594, d94041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94595 q = 1) : d94042 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94595, d94042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94595, d94042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94596 q = 1) : d94043 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94596, d94043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94596, d94043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94597 q = 1) : d94044 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94597, d94044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94597, d94044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94598 q = 1) : d94045 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94598, d94045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94598, d94045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21723 (p : Pattern) (ha : d92314 p = 1) (hb : d94604 p = 1) : d94051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94599 q = 1) : d94046 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94599, d94046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94599, d94046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21722 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94600 q = 1) : d94047 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94600, d94047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94600, d94047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94601 q = 1) : d94048 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94601, d94048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94601, d94048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94602 q = 1) : d94049 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94602, d94049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94602, d94049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94603 q = 1) : d94050 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94603, d94050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94603, d94050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94604 q = 1) : d94051 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94604, d94051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94604, d94051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21724 (p : Pattern) (ha : d92314 p = 1) (hb : d94609 p = 1) : d94056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1172 q = 1) (hb : d92314 q = 1) : d1172 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8759 q = 1) (hb : d92314 q = 1) : d93612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21517 q ha hb
    | true =>
      simp only [d8759, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8760 q = 1) (hb : d92314 q = 1) : d93613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8761 q = 1) (hb : d92314 q = 1) : d93614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8761, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8762 q = 1) (hb : d92314 q = 1) : d93615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8763 q = 1) (hb : d92314 q = 1) : d93616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94609 q = 1) : d94056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94609, d94056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94609, d94056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro21725 (p : Pattern) (ha : d92314 p = 1) (hb : d94618 p = 1) : d8888 p = 1 := by
  have h0 (q : Pattern) (ha : d8884 q = 1) (hb : d92313 q = 1) : d8884 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94615 q = 1) : d8885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92314, d94615, d8885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92314, d94615, d8885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94616 q = 1) : d8886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94616, d8886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94616, d8886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94617 q = 1) : d8887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94617, d8887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94617, d8887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94618 q = 1) : d8888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94618, d8888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94618, d8888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h6 p ha hb
theorem andIntro21726 (p : Pattern) (ha : d92314 p = 1) (hb : d94624 p = 1) : d94067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1497 q = 1) (hb : d92314 q = 1) : d1497 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94619 q = 1) : d94062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94619, d94062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21725 q ha hb
    | true =>
      simp only [d94619, d94062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94620 q = 1) : d94063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94620, d94063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94620, d94063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94621 q = 1) : d94064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94621, d94064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94621, d94064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94622 q = 1) : d94065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94622, d94065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94622, d94065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94623 q = 1) : d94066 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94623, d94066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94623, d94066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94624 q = 1) : d94067 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94624, d94067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94624, d94067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21727 (p : Pattern) (ha : d92314 p = 1) (hb : d94630 p = 1) : d94073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8765 q = 1) (hb : d92314 q = 1) : d93618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21516 q ha hb
    | true =>
      simp only [d8765, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21518 q ha hb
  have h2 (q : Pattern) (ha : d8766 q = 1) (hb : d92314 q = 1) : d93619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8766, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94607 q = 1) : d94054 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94607, d94054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94607, d94054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94608 q = 1) : d94055 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94608, d94055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94608, d94055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94610 q = 1) : d94057 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94610, d94057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94610, d94057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21724 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94611 q = 1) : d94058 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94611, d94058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94611, d94058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94612 q = 1) : d94059 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94612, d94059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94612, d94059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94613 q = 1) : d94060 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94613, d94060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94613, d94060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94614 q = 1) : d94061 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94614, d94061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94614, d94061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94625 q = 1) : d94068 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94625, d94068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94625, d94068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21726 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94626 q = 1) : d94069 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94626, d94069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94626, d94069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94627 q = 1) : d94070 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94627, d94070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94627, d94070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94628 q = 1) : d94071 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94628, d94071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94628, d94071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94629 q = 1) : d94072 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94629, d94072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94629, d94072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94630 q = 1) : d94073 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94630, d94073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94630, d94073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21728 (p : Pattern) (ha : d92314 p = 1) (hb : d94636 p = 1) : d94079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94631 q = 1) : d94074 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94631, d94074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94631, d94074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21727 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94632 q = 1) : d94075 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94632, d94075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94632, d94075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94633 q = 1) : d94076 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94633, d94076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94633, d94076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94634 q = 1) : d94077 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94634, d94077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94634, d94077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94635 q = 1) : d94078 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94635, d94078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94635, d94078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94636 q = 1) : d94079 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94636, d94079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94636, d94079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21729 (p : Pattern) (ha : d92314 p = 1) (hb : d94642 p = 1) : d94085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1633 q = 1) (hb : d92314 q = 1) : d1633 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8927 q = 1) (hb : d92314 q = 1) : d93720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21538 q ha hb
    | true =>
      simp only [d8927, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8928 q = 1) (hb : d92314 q = 1) : d93721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8929 q = 1) (hb : d92314 q = 1) : d93722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8929, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8930 q = 1) (hb : d92314 q = 1) : d93723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8931 q = 1) (hb : d92314 q = 1) : d93724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94642 q = 1) : d94085 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94642, d94085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94642, d94085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro21730 (p : Pattern) (ha : d92314 p = 1) (hb : d94651 p = 1) : d9056 p = 1 := by
  have h0 (q : Pattern) (ha : d9052 q = 1) (hb : d92313 q = 1) : d9052 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94648 q = 1) : d9053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92314, d94648, d9053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92314, d94648, d9053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94649 q = 1) : d9054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94649, d9054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94649, d9054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94650 q = 1) : d9055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94650, d9055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94650, d9055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94651 q = 1) : d9056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94651, d9056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94651, d9056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h6 p ha hb
theorem andIntro21731 (p : Pattern) (ha : d92314 p = 1) (hb : d94657 p = 1) : d94096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1974 q = 1) (hb : d92314 q = 1) : d1974 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94652 q = 1) : d94091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94652, d94091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21730 q ha hb
    | true =>
      simp only [d94652, d94091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94653 q = 1) : d94092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94653, d94092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94653, d94092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94654 q = 1) : d94093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94654, d94093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94654, d94093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94655 q = 1) : d94094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94655, d94094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94655, d94094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94656 q = 1) : d94095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94656, d94095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94656, d94095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94657 q = 1) : d94096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94657, d94096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94657, d94096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21732 (p : Pattern) (ha : d92314 p = 1) (hb : d94663 p = 1) : d94102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8933 q = 1) (hb : d92314 q = 1) : d93726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21537 q ha hb
    | true =>
      simp only [d8933, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21539 q ha hb
  have h2 (q : Pattern) (ha : d8934 q = 1) (hb : d92314 q = 1) : d93727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8934, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94640 q = 1) : d94083 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94640, d94083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94640, d94083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94641 q = 1) : d94084 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94641, d94084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94641, d94084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94643 q = 1) : d94086 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94643, d94086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94643, d94086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21729 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94644 q = 1) : d94087 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94644, d94087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94644, d94087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94645 q = 1) : d94088 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94645, d94088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94645, d94088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94646 q = 1) : d94089 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94646, d94089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94646, d94089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94647 q = 1) : d94090 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94647, d94090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94647, d94090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94658 q = 1) : d94097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94658, d94097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94658, d94097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21731 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94659 q = 1) : d94098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94659, d94098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94659, d94098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94660 q = 1) : d94099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94660, d94099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94660, d94099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94661 q = 1) : d94100 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94661, d94100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94661, d94100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94662 q = 1) : d94101 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94662, d94101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94662, d94101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94663 q = 1) : d94102 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94663, d94102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94663, d94102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21733 (p : Pattern) (ha : d92314 p = 1) (hb : d94669 p = 1) : d94108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94664 q = 1) : d94103 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94664, d94103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94664, d94103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21732 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94665 q = 1) : d94104 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94665, d94104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94665, d94104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94666 q = 1) : d94105 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94666, d94105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94666, d94105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94667 q = 1) : d94106 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94667, d94106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94667, d94106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94668 q = 1) : d94107 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94668, d94107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94668, d94107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94669 q = 1) : d94108 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94669, d94108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94669, d94108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21734 (p : Pattern) (ha : d92314 p = 1) (hb : d94676 p = 1) : d94115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2116 q = 1) (hb : d92314 q = 1) : d2116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9096 q = 1) (hb : d92314 q = 1) : d93829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21559 q ha hb
    | true =>
      simp only [d9096, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9097 q = 1) (hb : d92314 q = 1) : d93830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9098 q = 1) (hb : d92314 q = 1) : d93831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9098, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9099 q = 1) (hb : d92314 q = 1) : d93832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9100 q = 1) (hb : d92314 q = 1) : d93833 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94676 q = 1) : d94115 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94676, d94115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94676, d94115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro21735 (p : Pattern) (ha : d92314 p = 1) (hb : d94685 p = 1) : d9225 p = 1 := by
  have h0 (q : Pattern) (ha : d9221 q = 1) (hb : d92313 q = 1) : d9221 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2387 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94682 q = 1) : d9222 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92314, d94682, d9222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92314, d94682, d9222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94683 q = 1) : d9223 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94683, d9223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94683, d9223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94684 q = 1) : d9224 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94684, d9224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94684, d9224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94685 q = 1) : d9225 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94685, d9225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94685, d9225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h6 p ha hb
theorem andIntro21736 (p : Pattern) (ha : d92314 p = 1) (hb : d94691 p = 1) : d94126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2452 q = 1) (hb : d92314 q = 1) : d2452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94686 q = 1) : d94121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94686, d94121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21735 q ha hb
    | true =>
      simp only [d94686, d94121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94687 q = 1) : d94122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94687, d94122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94687, d94122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94688 q = 1) : d94123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94688, d94123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94688, d94123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94689 q = 1) : d94124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94689, d94124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94689, d94124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94690 q = 1) : d94125 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94690, d94125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94690, d94125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94691 q = 1) : d94126 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94691, d94126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94691, d94126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21737 (p : Pattern) (ha : d92314 p = 1) (hb : d94697 p = 1) : d94132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9102 q = 1) (hb : d92314 q = 1) : d93835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21558 q ha hb
    | true =>
      simp only [d9102, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21560 q ha hb
  have h2 (q : Pattern) (ha : d9103 q = 1) (hb : d92314 q = 1) : d93836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9103, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94674 q = 1) : d94113 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94674, d94113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94674, d94113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94675 q = 1) : d94114 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94675, d94114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94675, d94114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94677 q = 1) : d94116 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94677, d94116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94677, d94116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21734 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94678 q = 1) : d94117 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94678, d94117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94678, d94117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94679 q = 1) : d94118 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94679, d94118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94679, d94118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94680 q = 1) : d94119 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94680, d94119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94680, d94119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94681 q = 1) : d94120 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94681, d94120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94681, d94120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94692 q = 1) : d94127 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94692, d94127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94692, d94127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21736 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94693 q = 1) : d94128 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94693, d94128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94693, d94128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94694 q = 1) : d94129 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94694, d94129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94694, d94129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94695 q = 1) : d94130 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94695, d94130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94695, d94130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94696 q = 1) : d94131 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94696, d94131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94696, d94131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94697 q = 1) : d94132 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94697, d94132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94697, d94132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21738 (p : Pattern) (ha : d92314 p = 1) (hb : d94703 p = 1) : d94138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94698 q = 1) : d94133 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94698, d94133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94698, d94133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21737 q ha hb
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94699 q = 1) : d94134 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94699, d94134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94699, d94134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94700 q = 1) : d94135 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94700, d94135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94700, d94135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94701 q = 1) : d94136 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94701, d94136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94701, d94136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94702 q = 1) : d94137 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94702, d94137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94702, d94137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94703 q = 1) : d94138 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94703, d94138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94703, d94138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21739 (p : Pattern) (ha : d92314 p = 1) (hb : d94709 p = 1) : d94144 p = 1 := by
  have h0 (q : Pattern) (ha : d92314 q = 1) (hb : d94574 q = 1) : d94025 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94574, d94025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21713 q ha hb
    | true =>
      simp only [d94574, d94025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21718 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94605 q = 1) : d94052 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94605, d94052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94605, d94052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21723 q ha hb
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94606 q = 1) : d94053 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94606, d94053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94606, d94053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94637 q = 1) : d94080 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94637, d94080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94637, d94080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21728 q ha hb
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94638 q = 1) : d94081 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94638, d94081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94638, d94081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94639 q = 1) : d94082 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94639, d94082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94639, d94082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92314 q = 1) (hb : d94670 q = 1) : d94109 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94670, d94109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94670, d94109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21733 q ha hb
  have h8 (q : Pattern) (ha : d92314 q = 1) (hb : d94671 q = 1) : d94110 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94671, d94110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94671, d94110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92314 q = 1) (hb : d94672 q = 1) : d94111 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94672, d94111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94672, d94111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92314 q = 1) (hb : d94673 q = 1) : d94112 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94673, d94112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94673, d94112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92314 q = 1) (hb : d94704 q = 1) : d94139 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94704, d94139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94704, d94139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21738 q ha hb
  have h12 (q : Pattern) (ha : d92314 q = 1) (hb : d94705 q = 1) : d94140 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94705, d94140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94705, d94140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92314 q = 1) (hb : d94706 q = 1) : d94141 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94706, d94141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94706, d94141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92314 q = 1) (hb : d94707 q = 1) : d94142 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94707, d94142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94707, d94142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92314 q = 1) (hb : d94708 q = 1) : d94143 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94708, d94143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94708, d94143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92314 q = 1) (hb : d94709 q = 1) : d94144 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94709, d94144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94709, d94144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro21740 (p : Pattern) (ha : d92314 p = 1) (hb : d94715 p = 1) : d94150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94710 q = 1) : d94145 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94710, d94145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21739 q ha hb
    | true =>
      simp only [d94710, d94145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94711 q = 1) : d94146 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94711, d94146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94711, d94146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94712 q = 1) : d94147 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94712, d94147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94712, d94147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94713 q = 1) : d94148 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94713, d94148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94713, d94148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94714 q = 1) : d94149 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94714, d94149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94714, d94149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94715 q = 1) : d94150 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94715, d94150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94715, d94150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21741 (p : Pattern) (ha : d92314 p = 1) (hb : d94721 p = 1) : d94156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94716 q = 1) : d94151 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94716, d94151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21740 q ha hb
    | true =>
      simp only [d94716, d94151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94717 q = 1) : d94152 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94717, d94152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94717, d94152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94718 q = 1) : d94153 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94718, d94153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94718, d94153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94719 q = 1) : d94154 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94719, d94154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94719, d94154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94720 q = 1) : d94155 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94720, d94155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94720, d94155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94721 q = 1) : d94156 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94721, d94156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94721, d94156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21742 (p : Pattern) (ha : d92314 p = 1) (hb : d94727 p = 1) : d94162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94722 q = 1) : d94157 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94722, d94157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21741 q ha hb
    | true =>
      simp only [d94722, d94157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94723 q = 1) : d94158 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94723, d94158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94723, d94158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94724 q = 1) : d94159 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94724, d94159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94724, d94159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94725 q = 1) : d94160 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94725, d94160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94725, d94160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94726 q = 1) : d94161 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94726, d94161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94726, d94161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94727 q = 1) : d94162 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94727, d94162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94727, d94162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21743 (p : Pattern) (ha : d92314 p = 1) (hb : d94733 p = 1) : d94168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94728 q = 1) : d94163 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94728, d94163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21742 q ha hb
    | true =>
      simp only [d94728, d94163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94729 q = 1) : d94164 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94729, d94164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94729, d94164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92314 q = 1) (hb : d94730 q = 1) : d94165 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94730, d94165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94730, d94165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92314 q = 1) (hb : d94731 q = 1) : d94166 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94731, d94166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94731, d94166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92314 q = 1) (hb : d94732 q = 1) : d94167 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94732, d94167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94732, d94167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92314 q = 1) (hb : d94733 q = 1) : d94168 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94733, d94168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94733, d94168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21744 (p : Pattern) (ha : d92317 p = 1) (hb : d94739 p = 1) : d94174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92314 q = 1) (hb : d94734 q = 1) : d94169 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94734, d94169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21743 q ha hb
    | true =>
      simp only [d94734, d94169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92314 q = 1) (hb : d94735 q = 1) : d94170 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94735, d94170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94735, d94170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92316 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92317 q = 1) (hb : d94736 q = 1) : d94171 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d92317, d94736, d94171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92317, d94736, d94171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92317 q = 1) (hb : d94737 q = 1) : d94172 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94737, d94172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94737, d94172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92317 q = 1) (hb : d94738 q = 1) : d94173 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94738, d94173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94738, d94173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d92317 q = 1) (hb : d94739 q = 1) : d94174 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94739, d94174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94739, d94174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h8 p ha hb
theorem andIntro21745 (p : Pattern) (ha : d92317 p = 1) (hb : d94745 p = 1) : d94180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92317 q = 1) (hb : d94740 q = 1) : d94175 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94740, d94175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21744 q ha hb
    | true =>
      simp only [d94740, d94175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92317 q = 1) (hb : d94741 q = 1) : d94176 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94741, d94176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94741, d94176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92317 q = 1) (hb : d94742 q = 1) : d94177 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94742, d94177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94742, d94177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92317 q = 1) (hb : d94743 q = 1) : d94178 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94743, d94178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94743, d94178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92317 q = 1) (hb : d94744 q = 1) : d94179 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94744, d94179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94744, d94179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92317 q = 1) (hb : d94745 q = 1) : d94180 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94745, d94180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94745, d94180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21746 (p : Pattern) (ha : d92317 p = 1) (hb : d94751 p = 1) : d94186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92317 q = 1) (hb : d94746 q = 1) : d94181 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94746, d94181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21745 q ha hb
    | true =>
      simp only [d94746, d94181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92317 q = 1) (hb : d94747 q = 1) : d94182 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94747, d94182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94747, d94182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92317 q = 1) (hb : d94748 q = 1) : d94183 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94748, d94183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94748, d94183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92317 q = 1) (hb : d94749 q = 1) : d94184 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94749, d94184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94749, d94184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92317 q = 1) (hb : d94750 q = 1) : d94185 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94750, d94185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94750, d94185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92317 q = 1) (hb : d94751 q = 1) : d94186 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94751, d94186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94751, d94186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21747 (p : Pattern) (ha : d75708 p = 1) (hb : d93315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75692 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75698 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d75703 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d75631 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q hb ha
    | true =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d75704 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75704, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75704, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75705 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75705, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75705, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75706 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75706, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75706, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75707 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75707, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75707, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75708 q = 1) (hb : d93315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75708, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75708, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21748 (p : Pattern) (ha : d75724 p = 1) (hb : d93322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75692 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75698 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75703 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75631 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18939 q hb ha
    | true =>
      simp only [d75631, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d75704 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75704, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75704, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75705 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75705, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75705, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75706 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75706, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75706, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75707 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75707, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75707, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75713 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d75717 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d75719 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d75637 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75637, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18944 q hb ha
    | true =>
      simp only [d75637, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d75720 q = 1) (hb : d93318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75720, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75720, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75721 q = 1) (hb : d93319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75721, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75721, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75722 q = 1) (hb : d93320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75722, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d75722, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75723 q = 1) (hb : d93321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75723, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d75723, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75724 q = 1) (hb : d93322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75724, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75724, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21749 (p : Pattern) (ha : d75733 p = 1) (hb : d93976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75719 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75637 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75637, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18944 q hb ha
    | true =>
      simp only [d75637, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d75720 q = 1) (hb : d93318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75720, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75720, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75721 q = 1) (hb : d93319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75721, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75721, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75731 q = 1) (hb : d93320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75731, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75731, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75732 q = 1) (hb : d93321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75732, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75732, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75733 q = 1) (hb : d93976 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75733, d93976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75733, d93976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
