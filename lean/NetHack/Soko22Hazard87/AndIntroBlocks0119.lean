import NetHack.Soko22Hazard87.AndIntroBlocks0118
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro29750 (p : Pattern) (ha : d21948 p = 1) (hb : d147543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21755 q = 1) (hb : d147521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28195 q ha hb
    | true =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21756 q = 1) (hb : d147522 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21757 q = 1) (hb : d147523 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d147523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d147523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21758 q = 1) (hb : d147524 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d147524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21758, d147524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21776 q = 1) (hb : d147542 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21776, d147542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21776, d147542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21948 q = 1) (hb : d147543 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21948, d147543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21948, d147543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29751 (p : Pattern) (ha : d21765 p = 1) (hb : d147531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5012 q = 1) (hb : d69102 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5012, d69102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7946 q ha hb
    | true =>
      simp only [d5012, d69102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h4 (q : Pattern) (ha : d5013 q = 1) (hb : d69103 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5013, d69103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5013, d69103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d5014 q = 1) (hb : d69104 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5014, d69104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5014, d69104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d135 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5015 q = 1) (hb : d69105 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5015, d69105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5015, d69105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5016 q = 1) (hb : d69106 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5016, d69106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5016, d69106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d21765 q = 1) (hb : d147531 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21765, d147531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21765, d147531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h13 p ha hb
theorem andIntro29752 (p : Pattern) (ha : d147537 p = 1) (hb : d151871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21766 q = 1) (hb : d147532 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21766, d147532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29751 q ha hb
    | true =>
      simp only [d21766, d147532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21767 q = 1) (hb : d147533 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21767, d147533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21767, d147533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21768 q = 1) (hb : d147534 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21768, d147534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21768, d147534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21769 q = 1) (hb : d147535 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21769, d147535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21769, d147535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21770 q = 1) (hb : d147536 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21770, d147536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21770, d147536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147537 q = 1) (hb : d151871 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147537, d151871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d147537, d151871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro29753 (p : Pattern) (ha : d147549 p = 1) (hb : d151881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147528 q = 1) (hb : d151868 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147528, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28194 q ha hb
    | true =>
      simp only [d147528, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
  have h2 (q : Pattern) (ha : d147529 q = 1) (hb : d151869 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147529, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147529, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147530 q = 1) (hb : d151870 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147530, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147530, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147538 q = 1) (hb : d151872 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147538, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
    | true =>
      simp only [d147538, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29752 q ha hb
  have h5 (q : Pattern) (ha : d147539 q = 1) (hb : d151873 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147539, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147539, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147540 q = 1) (hb : d151874 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147540, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147540, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147541 q = 1) (hb : d151875 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147541, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147541, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147544 q = 1) (hb : d151876 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147544, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
    | true =>
      simp only [d147544, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29750 q hb ha
  have h9 (q : Pattern) (ha : d147545 q = 1) (hb : d151877 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147545, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147545, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147546 q = 1) (hb : d151878 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147546, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147546, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147547 q = 1) (hb : d151879 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147547, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147547, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147548 q = 1) (hb : d151880 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147548, d151880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147548, d151880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147549 q = 1) (hb : d151881 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147549, d151881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147549, d151881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29754 (p : Pattern) (ha : d147553 p = 1) (hb : d151885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147544 q = 1) (hb : d151876 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147544, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
    | true =>
      simp only [d147544, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29750 q hb ha
  have h2 (q : Pattern) (ha : d147545 q = 1) (hb : d151877 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147545, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147545, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147546 q = 1) (hb : d151878 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147546, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147546, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147547 q = 1) (hb : d151879 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147547, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147547, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147552 q = 1) (hb : d151884 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147552, d151884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147552, d151884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147553 q = 1) (hb : d151885 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147553, d151885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147553, d151885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29755 (p : Pattern) (ha : d147559 p = 1) (hb : d151891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d151882 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29753 q ha hb
    | true =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d151883 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d151888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147557 q = 1) (hb : d151889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147557, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147557, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147558 q = 1) (hb : d151890 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147558, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147558, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147559 q = 1) (hb : d151891 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147559, d151891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147559, d151891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29756 (p : Pattern) (ha : d147563 p = 1) (hb : d151895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d151892 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147561 q = 1) (hb : d151893 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147561, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147561, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147562 q = 1) (hb : d151894 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147562, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147562, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147563 q = 1) (hb : d151895 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147563, d151895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147563, d151895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29757 (p : Pattern) (ha : d147569 p = 1) (hb : d151901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147564 q = 1) (hb : d151896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29755 q ha hb
    | true =>
      simp only [d147564, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29756 q ha hb
  have h2 (q : Pattern) (ha : d147565 q = 1) (hb : d151897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147565, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147565, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147566 q = 1) (hb : d151898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147566, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147566, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147567 q = 1) (hb : d151899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147567, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147567, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147568 q = 1) (hb : d151900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147568, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147568, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147569 q = 1) (hb : d151901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147569, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147569, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29758 (p : Pattern) (ha : d147572 p = 1) (hb : d151904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d151882 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29753 q ha hb
    | true =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d151883 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d151888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147557 q = 1) (hb : d151889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147557, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147557, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147558 q = 1) (hb : d151890 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147558, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147558, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147572 q = 1) (hb : d151904 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147572, d151904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147572, d151904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29759 (p : Pattern) (ha : d147573 p = 1) (hb : d151905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d151892 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147561 q = 1) (hb : d151893 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147561, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147561, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147562 q = 1) (hb : d151894 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147562, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147562, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147573 q = 1) (hb : d151905 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147573, d151905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147573, d151905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29760 (p : Pattern) (ha : d147579 p = 1) (hb : d151911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147564 q = 1) (hb : d151896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29755 q ha hb
    | true =>
      simp only [d147564, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29756 q ha hb
  have h2 (q : Pattern) (ha : d147565 q = 1) (hb : d151897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147565, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147565, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147566 q = 1) (hb : d151898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147566, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147566, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147567 q = 1) (hb : d151899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147567, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147567, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147568 q = 1) (hb : d151900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147568, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147568, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147574 q = 1) (hb : d151906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29758 q ha hb
    | true =>
      simp only [d147574, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29759 q ha hb
  have h7 (q : Pattern) (ha : d147575 q = 1) (hb : d151907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147575, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147575, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147576 q = 1) (hb : d151908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147576, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147576, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147577 q = 1) (hb : d151909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147577, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147577, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147578 q = 1) (hb : d151910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147578, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147578, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147579 q = 1) (hb : d151911 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147579, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147579, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29761 (p : Pattern) (ha : d147584 p = 1) (hb : d151916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d151882 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29753 q ha hb
    | true =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d151883 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d151888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147557 q = 1) (hb : d151889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147557, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147557, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147583 q = 1) (hb : d151915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147583, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147583, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147584 q = 1) (hb : d151916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147584, d151916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147584, d151916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29762 (p : Pattern) (ha : d147586 p = 1) (hb : d151918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d151892 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147561 q = 1) (hb : d151893 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147561, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147561, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147585 q = 1) (hb : d151917 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147585, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147585, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147586 q = 1) (hb : d151918 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147586, d151918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147586, d151918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29763 (p : Pattern) (ha : d147593 p = 1) (hb : d151925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d151882 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29753 q ha hb
    | true =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d151883 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d151888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147591 q = 1) (hb : d151923 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147591, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147591, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147592 q = 1) (hb : d151924 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147592, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147592, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147593 q = 1) (hb : d151925 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147593, d151925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147593, d151925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29764 (p : Pattern) (ha : d147596 p = 1) (hb : d151928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d151892 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147594 q = 1) (hb : d151926 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147594, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147594, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147595 q = 1) (hb : d151927 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147595, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147595, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147596 q = 1) (hb : d151928 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147596, d151928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147596, d151928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29765 (p : Pattern) (ha : d13024 p = 1) (hb : d113354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9452 q = 1) (hb : d101067 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7946 q ha hb
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9795 q = 1) (hb : d101316 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9795, d101316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9795, d101316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9796 q = 1) (hb : d101317 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9797 q = 1) (hb : d101318 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9797, d101318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9797, d101318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9798 q = 1) (hb : d101319 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9798, d101319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9798, d101319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d13024 q = 1) (hb : d113354 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13024, d113354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13024, d113354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h11 p ha hb
theorem andIntro29766 (p : Pattern) (ha : d21850 p = 1) (hb : d147616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1088 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1089 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9772 q = 1) (hb : d101293 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23289 q ha hb
    | true =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h4 (q : Pattern) (ha : d9773 q = 1) (hb : d101294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9810 q = 1) (hb : d101331 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9810, d101331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9810, d101331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9811 q = 1) (hb : d101332 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9811, d101332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9811, d101332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9812 q = 1) (hb : d101333 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9812, d101333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9812, d101333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d21850 q = 1) (hb : d147616 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21850, d147616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21850, d147616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro29767 (p : Pattern) (ha : d147622 p = 1) (hb : d151935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21851 q = 1) (hb : d147617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21851, d147617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29766 q ha hb
    | true =>
      simp only [d21851, d147617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21852 q = 1) (hb : d147618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21852, d147618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21852, d147618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21853 q = 1) (hb : d147619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21853, d147619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21853, d147619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21854 q = 1) (hb : d147620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21854, d147620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21854, d147620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13025 q = 1) (hb : d113355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13026 q = 1) (hb : d113356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13027 q = 1) (hb : d113357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13028 q = 1) (hb : d113358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21855 q = 1) (hb : d147621 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21855, d147621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21855, d147621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147526 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d147622 q = 1) (hb : d151935 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147622, d151935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147622, d151935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro29768 (p : Pattern) (ha : d147628 p = 1) (hb : d151941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147613 q = 1) (hb : d151932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147613, d151932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28210 q ha hb
    | true =>
      simp only [d147613, d151932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28194 q ha hb
  have h2 (q : Pattern) (ha : d147614 q = 1) (hb : d151933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147614, d151933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147614, d151933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147615 q = 1) (hb : d151934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147615, d151934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147615, d151934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147623 q = 1) (hb : d151936 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147623, d151936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28194 q ha hb
    | true =>
      simp only [d147623, d151936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29767 q ha hb
  have h5 (q : Pattern) (ha : d147624 q = 1) (hb : d151937 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147624, d151937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147624, d151937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147625 q = 1) (hb : d151938 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147625, d151938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147625, d151938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147626 q = 1) (hb : d151939 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147626, d151939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147626, d151939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147528 q = 1) (hb : d151868 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147528, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28194 q ha hb
    | true =>
      simp only [d147528, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
  have h9 (q : Pattern) (ha : d147529 q = 1) (hb : d151869 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147529, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147529, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147530 q = 1) (hb : d151870 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147530, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147530, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147538 q = 1) (hb : d151872 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147538, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
    | true =>
      simp only [d147538, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29752 q ha hb
  have h12 (q : Pattern) (ha : d147539 q = 1) (hb : d151873 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147539, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147539, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147540 q = 1) (hb : d151874 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147540, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147540, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147541 q = 1) (hb : d151875 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147541, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147541, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147627 q = 1) (hb : d151940 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147627, d151940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147627, d151940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147628 q = 1) (hb : d151941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147628, d151941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147628, d151941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro29769 (p : Pattern) (ha : d147633 p = 1) (hb : d151946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147528 q = 1) (hb : d151868 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147528, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28194 q ha hb
    | true =>
      simp only [d147528, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
  have h2 (q : Pattern) (ha : d147529 q = 1) (hb : d151869 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147529, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147529, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147530 q = 1) (hb : d151870 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147530, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147530, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147538 q = 1) (hb : d151872 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147538, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
    | true =>
      simp only [d147538, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29752 q ha hb
  have h5 (q : Pattern) (ha : d147539 q = 1) (hb : d151873 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147539, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147539, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147540 q = 1) (hb : d151874 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147540, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147540, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147541 q = 1) (hb : d151875 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147541, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147541, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147631 q = 1) (hb : d151944 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147631, d151944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147631, d151944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147632 q = 1) (hb : d151945 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147632, d151945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147632, d151945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147633 q = 1) (hb : d151946 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147633, d151946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147633, d151946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29770 (p : Pattern) (ha : d147639 p = 1) (hb : d151952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147629 q = 1) (hb : d151942 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147629, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29768 q ha hb
    | true =>
      simp only [d147629, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147630 q = 1) (hb : d151943 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147630, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147630, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147634 q = 1) (hb : d151947 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147634, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29769 q ha hb
    | true =>
      simp only [d147634, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147635 q = 1) (hb : d151948 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147635, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147635, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147636 q = 1) (hb : d151949 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147636, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147636, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147637 q = 1) (hb : d151950 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147637, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147637, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147638 q = 1) (hb : d151951 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147638, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147638, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147639 q = 1) (hb : d151952 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147639, d151952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147639, d151952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29771 (p : Pattern) (ha : d147643 p = 1) (hb : d151956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147634 q = 1) (hb : d151947 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147634, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29769 q ha hb
    | true =>
      simp only [d147634, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147635 q = 1) (hb : d151948 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147635, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147635, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147640 q = 1) (hb : d151953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147640, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147640, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147641 q = 1) (hb : d151954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147641, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147641, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147642 q = 1) (hb : d151955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147642, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147642, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147643 q = 1) (hb : d151956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147643, d151956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147643, d151956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29772 (p : Pattern) (ha : d21948 p = 1) (hb : d147646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21755 q = 1) (hb : d147521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28195 q ha hb
    | true =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21756 q = 1) (hb : d147522 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21757 q = 1) (hb : d147523 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d147523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d147523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21758 q = 1) (hb : d147524 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d147524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21758, d147524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21776 q = 1) (hb : d147542 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21776, d147542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21776, d147542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21948 q = 1) (hb : d147646 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21948, d147646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21948, d147646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29773 (p : Pattern) (ha : d147652 p = 1) (hb : d151881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147528 q = 1) (hb : d151868 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147528, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28194 q ha hb
    | true =>
      simp only [d147528, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
  have h2 (q : Pattern) (ha : d147529 q = 1) (hb : d151869 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147529, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147529, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147530 q = 1) (hb : d151870 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147530, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147530, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147538 q = 1) (hb : d151872 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147538, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
    | true =>
      simp only [d147538, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29752 q ha hb
  have h5 (q : Pattern) (ha : d147539 q = 1) (hb : d151873 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147539, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147539, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147540 q = 1) (hb : d151874 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147540, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147540, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147541 q = 1) (hb : d151875 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147541, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147541, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147647 q = 1) (hb : d151876 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147647, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28196 q ha hb
    | true =>
      simp only [d147647, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29772 q hb ha
  have h9 (q : Pattern) (ha : d147648 q = 1) (hb : d151877 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147648, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147648, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147649 q = 1) (hb : d151878 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147649, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147649, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147650 q = 1) (hb : d151879 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147650, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147650, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147651 q = 1) (hb : d151880 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147651, d151880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147651, d151880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147652 q = 1) (hb : d151881 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147652, d151881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147652, d151881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29774 (p : Pattern) (ha : d147658 p = 1) (hb : d151962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147653 q = 1) (hb : d151882 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147653, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29773 q ha hb
    | true =>
      simp only [d147653, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147654 q = 1) (hb : d151883 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147654, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147654, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147655 q = 1) (hb : d151959 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147655, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147655, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147656 q = 1) (hb : d151960 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147656, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147656, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147657 q = 1) (hb : d151961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147657, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147657, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147658 q = 1) (hb : d151962 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147658, d151962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147658, d151962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29775 (p : Pattern) (ha : d147664 p = 1) (hb : d151968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147587 q = 1) (hb : d151919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147587, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29761 q ha hb
    | true =>
      simp only [d147587, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29762 q ha hb
  have h2 (q : Pattern) (ha : d147588 q = 1) (hb : d151920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147588, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147588, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147589 q = 1) (hb : d151921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147589, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147589, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147590 q = 1) (hb : d151922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147590, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147590, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147597 q = 1) (hb : d151929 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147597, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29763 q ha hb
    | true =>
      simp only [d147597, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29764 q ha hb
  have h6 (q : Pattern) (ha : d147598 q = 1) (hb : d151930 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147598, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147598, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147599 q = 1) (hb : d151931 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147599, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147599, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147644 q = 1) (hb : d151957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147644, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29770 q ha hb
    | true =>
      simp only [d147644, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29771 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147564 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147645 q = 1) (hb : d151958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147645, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147659 q = 1) (hb : d151963 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147659, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29774 q ha hb
    | true =>
      simp only [d147659, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147660 q = 1) (hb : d151964 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147660, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147660, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147661 q = 1) (hb : d151965 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147661, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147662 q = 1) (hb : d151966 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147662, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147663 q = 1) (hb : d151967 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147663, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147664 q = 1) (hb : d151968 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147664, d151968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147664, d151968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro29776 (p : Pattern) (ha : d147665 p = 1) (hb : d151969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d151882 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29753 q ha hb
    | true =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d151883 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d151888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147557 q = 1) (hb : d151889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147557, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147557, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147583 q = 1) (hb : d151915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147583, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147583, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147665 q = 1) (hb : d151969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147665, d151969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147665, d151969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29777 (p : Pattern) (ha : d147666 p = 1) (hb : d151970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d151892 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147561 q = 1) (hb : d151893 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147561, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147561, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147585 q = 1) (hb : d151917 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147585, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147585, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147666 q = 1) (hb : d151970 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147666, d151970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147666, d151970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29778 (p : Pattern) (ha : d147671 p = 1) (hb : d151975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d151882 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29753 q ha hb
    | true =>
      simp only [d147550, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d151883 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d151888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147591 q = 1) (hb : d151923 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147591, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147591, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147592 q = 1) (hb : d151924 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147592, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147592, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147671 q = 1) (hb : d151975 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147671, d151975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147671, d151975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29779 (p : Pattern) (ha : d147672 p = 1) (hb : d151976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d151892 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147594 q = 1) (hb : d151926 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147594, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147594, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147595 q = 1) (hb : d151927 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147595, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147595, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147672 q = 1) (hb : d151976 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147672, d151976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147672, d151976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29780 (p : Pattern) (ha : d147676 p = 1) (hb : d151980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147629 q = 1) (hb : d151942 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147629, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29768 q ha hb
    | true =>
      simp only [d147629, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147630 q = 1) (hb : d151943 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147630, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147630, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147634 q = 1) (hb : d151947 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147634, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29769 q ha hb
    | true =>
      simp only [d147634, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147635 q = 1) (hb : d151948 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147635, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147635, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147636 q = 1) (hb : d151949 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147636, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147636, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147637 q = 1) (hb : d151950 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147637, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147637, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147638 q = 1) (hb : d151951 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147638, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147638, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147676 q = 1) (hb : d151980 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147676, d151980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147676, d151980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29781 (p : Pattern) (ha : d147677 p = 1) (hb : d151981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147634 q = 1) (hb : d151947 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147634, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29769 q ha hb
    | true =>
      simp only [d147634, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147635 q = 1) (hb : d151948 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147635, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147635, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d151886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29754 q ha hb
    | true =>
      simp only [d147554, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d151887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147640 q = 1) (hb : d151953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147640, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147640, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147641 q = 1) (hb : d151954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147641, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147641, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147642 q = 1) (hb : d151955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147642, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147642, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147677 q = 1) (hb : d151981 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147677, d151981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147677, d151981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29782 (p : Pattern) (ha : d147680 p = 1) (hb : d151984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147653 q = 1) (hb : d151882 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147653, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29773 q ha hb
    | true =>
      simp only [d147653, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147654 q = 1) (hb : d151883 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147654, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147654, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147655 q = 1) (hb : d151959 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147655, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147655, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147656 q = 1) (hb : d151960 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147656, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147656, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147657 q = 1) (hb : d151961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147657, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147657, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147680 q = 1) (hb : d151984 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147680, d151984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147680, d151984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29783 (p : Pattern) (ha : d147686 p = 1) (hb : d151990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147587 q = 1) (hb : d151919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147587, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29761 q ha hb
    | true =>
      simp only [d147587, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29762 q ha hb
  have h2 (q : Pattern) (ha : d147588 q = 1) (hb : d151920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147588, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147588, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147589 q = 1) (hb : d151921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147589, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147589, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147590 q = 1) (hb : d151922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147590, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147590, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147597 q = 1) (hb : d151929 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147597, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29763 q ha hb
    | true =>
      simp only [d147597, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29764 q ha hb
  have h6 (q : Pattern) (ha : d147598 q = 1) (hb : d151930 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147598, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147598, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147599 q = 1) (hb : d151931 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147599, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147599, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147644 q = 1) (hb : d151957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147644, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29770 q ha hb
    | true =>
      simp only [d147644, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29771 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147564 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147645 q = 1) (hb : d151958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147645, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147659 q = 1) (hb : d151963 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147659, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29774 q ha hb
    | true =>
      simp only [d147659, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147660 q = 1) (hb : d151964 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147660, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147660, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147661 q = 1) (hb : d151965 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147661, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147662 q = 1) (hb : d151966 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147662, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147663 q = 1) (hb : d151967 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147663, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147667 q = 1) (hb : d151971 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147667, d151971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29776 q ha hb
    | true =>
      simp only [d147667, d151971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29777 q ha hb
  have h17 (q : Pattern) (ha : d147668 q = 1) (hb : d151972 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147668, d151972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147668, d151972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147669 q = 1) (hb : d151973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147669, d151973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147669, d151973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d147670 q = 1) (hb : d151974 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147670, d151974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147670, d151974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147673 q = 1) (hb : d151977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147673, d151977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29778 q ha hb
    | true =>
      simp only [d147673, d151977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29779 q ha hb
  have h21 (q : Pattern) (ha : d147674 q = 1) (hb : d151978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147674, d151978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147674, d151978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d147675 q = 1) (hb : d151979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147675, d151979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147675, d151979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147678 q = 1) (hb : d151982 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147678, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29780 q ha hb
    | true =>
      simp only [d147678, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29781 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d147574 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d147679 q = 1) (hb : d151983 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d147679, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d147681 q = 1) (hb : d151985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147681, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29782 q ha hb
    | true =>
      simp only [d147681, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d147682 q = 1) (hb : d151986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147682, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d147682, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d147683 q = 1) (hb : d151987 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d147683, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d147684 q = 1) (hb : d151988 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147684, d151988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d147684, d151988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d147685 q = 1) (hb : d151989 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147685, d151989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147685, d151989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d147686 q = 1) (hb : d151990 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147686, d151990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147686, d151990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro29784 (p : Pattern) (ha : d147698 p = 1) (hb : d152002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147688 q = 1) (hb : d151992 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147688, d151992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29771 q ha hb
    | true =>
      simp only [d147688, d151992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29756 q ha hb
  have h2 (q : Pattern) (ha : d147689 q = 1) (hb : d151993 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147689, d151993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147689, d151993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147690 q = 1) (hb : d151994 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147690, d151994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147690, d151994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147691 q = 1) (hb : d151995 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147691, d151995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147691, d151995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147692 q = 1) (hb : d151996 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147692, d151996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147692, d151996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147693 q = 1) (hb : d151997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147693, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29756 q ha hb
    | true =>
      simp only [d147693, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147694 q = 1) (hb : d151998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147694, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147694, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147695 q = 1) (hb : d151999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147695, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147695, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147696 q = 1) (hb : d152000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147696, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147696, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147697 q = 1) (hb : d152001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147697, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147697, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147698 q = 1) (hb : d152002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147698, d152002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147698, d152002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29785 (p : Pattern) (ha : d147704 p = 1) (hb : d152008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147693 q = 1) (hb : d151997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147693, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29756 q ha hb
    | true =>
      simp only [d147693, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147694 q = 1) (hb : d151998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147694, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147694, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147695 q = 1) (hb : d151999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147695, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147695, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147696 q = 1) (hb : d152000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147696, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147696, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147697 q = 1) (hb : d152001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147697, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147697, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147699 q = 1) (hb : d152003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147699, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29759 q ha hb
    | true =>
      simp only [d147699, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147700 q = 1) (hb : d152004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147700, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147700, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147701 q = 1) (hb : d152005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147701, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147701, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147702 q = 1) (hb : d152006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147702, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147702, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147703 q = 1) (hb : d152007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147703, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147703, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147704 q = 1) (hb : d152008 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147704, d152008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147704, d152008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29786 (p : Pattern) (ha : d147711 p = 1) (hb : d152015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147678 q = 1) (hb : d151982 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147678, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29780 q ha hb
    | true =>
      simp only [d147678, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29781 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147574 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147679 q = 1) (hb : d151983 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147679, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147681 q = 1) (hb : d151985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147681, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29782 q ha hb
    | true =>
      simp only [d147681, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147682 q = 1) (hb : d151986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147682, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147682, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147683 q = 1) (hb : d151987 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147683, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147709 q = 1) (hb : d152013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147709, d152013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147709, d152013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147710 q = 1) (hb : d152014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147710, d152014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147710, d152014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147711 q = 1) (hb : d152015 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147711, d152015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147711, d152015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29787 (p : Pattern) (ha : d147713 p = 1) (hb : d152017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147699 q = 1) (hb : d152003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147699, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29759 q ha hb
    | true =>
      simp only [d147699, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147700 q = 1) (hb : d152004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147700, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147700, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147701 q = 1) (hb : d152005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147701, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147701, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147702 q = 1) (hb : d152006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147702, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147702, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147703 q = 1) (hb : d152007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147703, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147703, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147713 q = 1) (hb : d152017 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147713, d152017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147713, d152017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29788 (p : Pattern) (ha : d147754 p = 1) (hb : d152026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22053 q = 1) (hb : d147748 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22053, d147748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22053, d147748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29766 q ha hb
  have h2 (q : Pattern) (ha : d21851 q = 1) (hb : d147617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21851, d147617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29766 q ha hb
    | true =>
      simp only [d21851, d147617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22054 q = 1) (hb : d147749 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22054, d147749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22054, d147749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21852 q = 1) (hb : d147618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21852, d147618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21852, d147618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22055 q = 1) (hb : d147750 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22055, d147750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22055, d147750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22056 q = 1) (hb : d147751 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22056, d147751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22056, d147751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13164 q = 1) (hb : d113456 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
  have h8 (q : Pattern) (ha : d13025 q = 1) (hb : d113355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13165 q = 1) (hb : d113457 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13026 q = 1) (hb : d113356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13166 q = 1) (hb : d113458 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13167 q = 1) (hb : d113459 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22057 q = 1) (hb : d147752 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22057, d147752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22057, d147752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147753 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147754 q = 1) (hb : d152026 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147754, d152026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d147754, d152026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro29789 (p : Pattern) (ha : d147773 p = 1) (hb : d152034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22073 q = 1) (hb : d147768 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22073, d147768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22073, d147768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29751 q ha hb
  have h2 (q : Pattern) (ha : d21766 q = 1) (hb : d147532 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21766, d147532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29751 q ha hb
    | true =>
      simp only [d21766, d147532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22074 q = 1) (hb : d147769 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22074, d147769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22074, d147769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21767 q = 1) (hb : d147533 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21767, d147533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21767, d147533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22075 q = 1) (hb : d147770 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22075, d147770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22075, d147770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22076 q = 1) (hb : d147771 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22076, d147771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22076, d147771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22077 q = 1) (hb : d147772 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22077, d147772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22077, d147772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147773 q = 1) (hb : d152034 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147773, d152034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d147773, d152034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro29790 (p : Pattern) (ha : d147779 p = 1) (hb : d152040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147745 q = 1) (hb : d152023 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147745, d152023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28230 q ha hb
    | true =>
      simp only [d147745, d152023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28231 q ha hb
  have h2 (q : Pattern) (ha : d147746 q = 1) (hb : d152024 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147746, d152024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147746, d152024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147747 q = 1) (hb : d152025 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147747, d152025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147747, d152025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147755 q = 1) (hb : d152027 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147755, d152027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28231 q ha hb
    | true =>
      simp only [d147755, d152027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29788 q ha hb
  have h5 (q : Pattern) (ha : d147756 q = 1) (hb : d152028 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147756, d152028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147756, d152028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147757 q = 1) (hb : d152029 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147757, d152029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147757, d152029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147758 q = 1) (hb : d152030 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147758, d152030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147758, d152030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147765 q = 1) (hb : d152031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28231 q ha hb
    | true =>
      simp only [d147765, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
  have h9 (q : Pattern) (ha : d147766 q = 1) (hb : d152032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147767 q = 1) (hb : d152033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147774 q = 1) (hb : d152035 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
    | true =>
      simp only [d147774, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29789 q ha hb
  have h12 (q : Pattern) (ha : d147775 q = 1) (hb : d152036 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147776 q = 1) (hb : d152037 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147777 q = 1) (hb : d152038 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147777, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147778 q = 1) (hb : d152039 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147778, d152039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147778, d152039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147779 q = 1) (hb : d152040 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147779, d152040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147779, d152040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro29791 (p : Pattern) (ha : d147784 p = 1) (hb : d152045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147765 q = 1) (hb : d152031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28231 q ha hb
    | true =>
      simp only [d147765, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
  have h2 (q : Pattern) (ha : d147766 q = 1) (hb : d152032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147767 q = 1) (hb : d152033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147774 q = 1) (hb : d152035 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
    | true =>
      simp only [d147774, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29789 q ha hb
  have h5 (q : Pattern) (ha : d147775 q = 1) (hb : d152036 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147776 q = 1) (hb : d152037 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147777 q = 1) (hb : d152038 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147777, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147782 q = 1) (hb : d152043 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147782, d152043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147782, d152043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147783 q = 1) (hb : d152044 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147783, d152044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147783, d152044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147784 q = 1) (hb : d152045 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147784, d152045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147784, d152045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29792 (p : Pattern) (ha : d147790 p = 1) (hb : d152051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147780 q = 1) (hb : d152041 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147780, d152041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29790 q ha hb
    | true =>
      simp only [d147780, d152041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147781 q = 1) (hb : d152042 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147781, d152042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147781, d152042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147785 q = 1) (hb : d152046 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147785, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29791 q ha hb
    | true =>
      simp only [d147785, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147786 q = 1) (hb : d152047 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147786, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147786, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147787 q = 1) (hb : d152048 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147787, d152048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147787, d152048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147788 q = 1) (hb : d152049 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147788, d152049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147788, d152049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147789 q = 1) (hb : d152050 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147789, d152050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147789, d152050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147790 q = 1) (hb : d152051 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147790, d152051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147790, d152051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29793 (p : Pattern) (ha : d22174 p = 1) (hb : d147792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22064 q = 1) (hb : d147759 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d147759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22064, d147759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28195 q ha hb
  have h2 (q : Pattern) (ha : d21755 q = 1) (hb : d147521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28195 q ha hb
    | true =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22065 q = 1) (hb : d147760 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d147760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22065, d147760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21756 q = 1) (hb : d147522 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22066 q = 1) (hb : d147761 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d147761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22066, d147761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22067 q = 1) (hb : d147762 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d147762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22067, d147762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22096 q = 1) (hb : d147791 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22096, d147791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22096, d147791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d22174 q = 1) (hb : d147792 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22174, d147792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22174, d147792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29794 (p : Pattern) (ha : d147798 p = 1) (hb : d152057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147793 q = 1) (hb : d152052 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147793, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
    | true =>
      simp only [d147793, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29793 q hb ha
  have h2 (q : Pattern) (ha : d147794 q = 1) (hb : d152053 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147794, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147794, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147795 q = 1) (hb : d152054 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147795, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147795, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147796 q = 1) (hb : d152055 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147796, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147796, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147797 q = 1) (hb : d152056 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147797, d152056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147797, d152056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147798 q = 1) (hb : d152057 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147798, d152057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147798, d152057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29795 (p : Pattern) (ha : d147804 p = 1) (hb : d152063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147785 q = 1) (hb : d152046 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147785, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29791 q ha hb
    | true =>
      simp only [d147785, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147786 q = 1) (hb : d152047 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147786, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147786, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147799 q = 1) (hb : d152058 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147799, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29794 q ha hb
    | true =>
      simp only [d147799, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147800 q = 1) (hb : d152059 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147800, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147800, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147801 q = 1) (hb : d152060 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147801, d152060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147801, d152060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147802 q = 1) (hb : d152061 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147802, d152061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147802, d152061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147803 q = 1) (hb : d152062 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147803, d152062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147803, d152062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147804 q = 1) (hb : d152063 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147804, d152063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147804, d152063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29796 (p : Pattern) (ha : d22174 p = 1) (hb : d147820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22064 q = 1) (hb : d147759 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d147759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22064, d147759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28195 q ha hb
  have h2 (q : Pattern) (ha : d21755 q = 1) (hb : d147521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28195 q ha hb
    | true =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22065 q = 1) (hb : d147760 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d147760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22065, d147760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21756 q = 1) (hb : d147522 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22066 q = 1) (hb : d147761 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d147761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22066, d147761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22067 q = 1) (hb : d147762 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d147762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22067, d147762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22096 q = 1) (hb : d147791 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22096, d147791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22096, d147791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22174 q = 1) (hb : d147820 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22174, d147820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22174, d147820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29797 (p : Pattern) (ha : d147826 p = 1) (hb : d152067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147765 q = 1) (hb : d152031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28231 q ha hb
    | true =>
      simp only [d147765, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
  have h2 (q : Pattern) (ha : d147766 q = 1) (hb : d152032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147767 q = 1) (hb : d152033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147774 q = 1) (hb : d152035 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
    | true =>
      simp only [d147774, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29789 q ha hb
  have h5 (q : Pattern) (ha : d147775 q = 1) (hb : d152036 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147776 q = 1) (hb : d152037 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147777 q = 1) (hb : d152038 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147777, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147821 q = 1) (hb : d152052 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147821, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
    | true =>
      simp only [d147821, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29796 q hb ha
  have h9 (q : Pattern) (ha : d147822 q = 1) (hb : d152053 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147822, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147822, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147823 q = 1) (hb : d152054 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147823, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147823, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147824 q = 1) (hb : d152055 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147824, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147824, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147825 q = 1) (hb : d152066 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147825, d152066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147825, d152066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147826 q = 1) (hb : d152067 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147826, d152067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147826, d152067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29798 (p : Pattern) (ha : d147832 p = 1) (hb : d152073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147827 q = 1) (hb : d152068 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147827, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29797 q ha hb
    | true =>
      simp only [d147827, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147828 q = 1) (hb : d152069 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147828, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147828, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147829 q = 1) (hb : d152070 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147829, d152070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147829, d152070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147830 q = 1) (hb : d152071 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147830, d152071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147830, d152071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147831 q = 1) (hb : d152072 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147831, d152072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147831, d152072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147832 q = 1) (hb : d152073 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147832, d152073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147832, d152073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29799 (p : Pattern) (ha : d147838 p = 1) (hb : d152079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147805 q = 1) (hb : d152064 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147805, d152064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29792 q ha hb
    | true =>
      simp only [d147805, d152064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29795 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147819 q = 1) (hb : d152065 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147819, d152065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147819, d152065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147833 q = 1) (hb : d152074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147833, d152074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29798 q ha hb
    | true =>
      simp only [d147833, d152074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147834 q = 1) (hb : d152075 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147834, d152075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147834, d152075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147835 q = 1) (hb : d152076 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147835, d152076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147835, d152076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147836 q = 1) (hb : d152077 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147836, d152077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147836, d152077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147837 q = 1) (hb : d152078 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147837, d152078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147837, d152078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147838 q = 1) (hb : d152079 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147838, d152079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147838, d152079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29800 (p : Pattern) (ha : d147817 p = 1) (hb : d152084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147799 q = 1) (hb : d152058 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147799, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29794 q ha hb
    | true =>
      simp only [d147799, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147800 q = 1) (hb : d152059 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147800, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147800, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147814 q = 1) (hb : d152081 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147814, d152081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147814, d152081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147815 q = 1) (hb : d152082 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147815, d152082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147815, d152082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147816 q = 1) (hb : d152083 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147816, d152083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147816, d152083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147817 q = 1) (hb : d152084 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147817, d152084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147817, d152084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29801 (p : Pattern) (ha : d147845 p = 1) (hb : d152090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147840 q = 1) (hb : d152085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147840, d152085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29800 q ha hb
    | true =>
      simp only [d147840, d152085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147841 q = 1) (hb : d152086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147841, d152086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147841, d152086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147842 q = 1) (hb : d152087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147842, d152087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147842, d152087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147843 q = 1) (hb : d152088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147843, d152088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147843, d152088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147844 q = 1) (hb : d152089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147844, d152089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147844, d152089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147845 q = 1) (hb : d152090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147845, d152090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147845, d152090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29802 (p : Pattern) (ha : d147851 p = 1) (hb : d152096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147570 q = 1) (hb : d151902 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147570, d151902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147570, d151902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29757 q ha hb
  have h2 (q : Pattern) (ha : d147571 q = 1) (hb : d151903 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147571, d151903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147571, d151903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d147580 q = 1) (hb : d151912 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147580, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29757 q ha hb
    | true =>
      simp only [d147580, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29760 q ha hb
  have h4 (q : Pattern) (ha : d147581 q = 1) (hb : d151913 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147581, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147581, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147582 q = 1) (hb : d151914 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147582, d151914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147582, d151914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147687 q = 1) (hb : d151991 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147687, d151991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29775 q ha hb
    | true =>
      simp only [d147687, d151991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29783 q ha hb
  have h7 (q : Pattern) (ha : d147705 q = 1) (hb : d152009 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147705, d152009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29784 q ha hb
    | true =>
      simp only [d147705, d152009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29785 q ha hb
  have h8 (q : Pattern) (ha : d147706 q = 1) (hb : d152010 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147706, d152010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147706, d152010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147707 q = 1) (hb : d152011 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147707, d152011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147707, d152011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d147708 q = 1) (hb : d152012 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147708, d152012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147708, d152012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147712 q = 1) (hb : d152016 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147712, d152016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147712, d152016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29786 q ha hb
  have h12 (q : Pattern) (ha : d147714 q = 1) (hb : d152018 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147714, d152018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147714, d152018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29787 q ha hb
  have h13 (q : Pattern) (ha : d147715 q = 1) (hb : d152019 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147715, d152019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147715, d152019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147716 q = 1) (hb : d152020 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147716, d152020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147716, d152020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d147717 q = 1) (hb : d152021 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147717, d152021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d147717, d152021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d147718 q = 1) (hb : d152022 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147718, d152022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147718, d152022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147839 q = 1) (hb : d152080 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147839, d152080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147839, d152080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29799 q ha hb
  have h18 (q : Pattern) (ha : d147846 q = 1) (hb : d152091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147846, d152091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147846, d152091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29801 q ha hb
  have h19 (q : Pattern) (ha : d147847 q = 1) (hb : d152092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147847, d152092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147847, d152092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147848 q = 1) (hb : d152093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147848, d152093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147848, d152093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d147849 q = 1) (hb : d152094 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147849, d152094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d147849, d152094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d147850 q = 1) (hb : d152095 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147850, d152095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147850, d152095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147851 q = 1) (hb : d152096 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147851, d152096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147851, d152096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29803 (p : Pattern) (ha : d147857 p = 1) (hb : d152102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147852 q = 1) (hb : d152097 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147852, d152097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147852, d152097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29802 q ha hb
  have h2 (q : Pattern) (ha : d147853 q = 1) (hb : d152098 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147853, d152098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147853, d152098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147854 q = 1) (hb : d152099 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147854, d152099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147854, d152099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147855 q = 1) (hb : d152100 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147855, d152100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147855, d152100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147856 q = 1) (hb : d152101 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147856, d152101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147856, d152101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147857 q = 1) (hb : d152102 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147857, d152102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147857, d152102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29804 (p : Pattern) (ha : d22421 p = 1) (hb : d147897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22233 q = 1) (hb : d147875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
    | true =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22234 q = 1) (hb : d147876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22235 q = 1) (hb : d147877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22235, d147877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22235, d147877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22236 q = 1) (hb : d147878 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22236, d147878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22236, d147878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22254 q = 1) (hb : d147896 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22254, d147896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22254, d147896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22421 q = 1) (hb : d147897 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22421, d147897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22421, d147897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29805 (p : Pattern) (ha : d22243 p = 1) (hb : d147885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5123 q = 1) (hb : d69210 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5123, d69210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7963 q ha hb
    | true =>
      simp only [d5123, d69210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h5 (q : Pattern) (ha : d5124 q = 1) (hb : d69211 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5124, d69211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5124, d69211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5125 q = 1) (hb : d69212 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5125, d69212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5125, d69212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1549 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1550 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1566 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1566, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5126 q = 1) (hb : d69213 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5126, d69213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5126, d69213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5127 q = 1) (hb : d69214 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5127, d69214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5127, d69214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22243 q = 1) (hb : d147885 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22243, d147885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22243, d147885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h14 p ha hb
theorem andIntro29806 (p : Pattern) (ha : d147891 p = 1) (hb : d152109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22244 q = 1) (hb : d147886 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22244, d147886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29805 q ha hb
    | true =>
      simp only [d22244, d147886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22245 q = 1) (hb : d147887 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22245, d147887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22245, d147887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22246 q = 1) (hb : d147888 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22246, d147888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22246, d147888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22247 q = 1) (hb : d147889 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22247, d147889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22247, d147889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22248 q = 1) (hb : d147890 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22248, d147890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22248, d147890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147891 q = 1) (hb : d152109 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147891, d152109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d147891, d152109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro29807 (p : Pattern) (ha : d147903 p = 1) (hb : d152119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147882 q = 1) (hb : d152106 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28246 q ha hb
    | true =>
      simp only [d147882, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
  have h2 (q : Pattern) (ha : d147883 q = 1) (hb : d152107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147884 q = 1) (hb : d152108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147892 q = 1) (hb : d152110 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147892, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29806 q ha hb
  have h5 (q : Pattern) (ha : d147893 q = 1) (hb : d152111 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147894 q = 1) (hb : d152112 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147895 q = 1) (hb : d152113 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147895, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147898 q = 1) (hb : d152114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147898, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147898, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29804 q hb ha
  have h9 (q : Pattern) (ha : d147899 q = 1) (hb : d152115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147899, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147899, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147900 q = 1) (hb : d152116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147900, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147900, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147901 q = 1) (hb : d152117 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147901, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147901, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147902 q = 1) (hb : d152118 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147902, d152118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147902, d152118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147903 q = 1) (hb : d152119 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147903, d152119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147903, d152119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29808 (p : Pattern) (ha : d147907 p = 1) (hb : d152123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147898 q = 1) (hb : d152114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147898, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147898, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29804 q hb ha
  have h2 (q : Pattern) (ha : d147899 q = 1) (hb : d152115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147899, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147899, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147900 q = 1) (hb : d152116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147900, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147900, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147901 q = 1) (hb : d152117 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147901, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147901, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147906 q = 1) (hb : d152122 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147906, d152122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147906, d152122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147907 q = 1) (hb : d152123 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147907, d152123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147907, d152123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29809 (p : Pattern) (ha : d147913 p = 1) (hb : d152129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d152120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29807 q ha hb
    | true =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d152121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d152126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d152127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147912 q = 1) (hb : d152128 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147912, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147912, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147913 q = 1) (hb : d152129 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147913, d152129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147913, d152129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29810 (p : Pattern) (ha : d147917 p = 1) (hb : d152133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d152130 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d152131 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147916 q = 1) (hb : d152132 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147916, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147916, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147917 q = 1) (hb : d152133 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147917, d152133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147917, d152133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29811 (p : Pattern) (ha : d147923 p = 1) (hb : d152139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147918 q = 1) (hb : d152134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29809 q ha hb
    | true =>
      simp only [d147918, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29810 q ha hb
  have h2 (q : Pattern) (ha : d147919 q = 1) (hb : d152135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147919, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147919, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147920 q = 1) (hb : d152136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147920, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147920, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147921 q = 1) (hb : d152137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147921, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147921, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147922 q = 1) (hb : d152138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147922, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147922, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147923 q = 1) (hb : d152139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147923, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147923, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29812 (p : Pattern) (ha : d147926 p = 1) (hb : d152142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d152120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29807 q ha hb
    | true =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d152121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d152126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d152127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147912 q = 1) (hb : d152128 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147912, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147912, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147926 q = 1) (hb : d152142 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147926, d152142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147926, d152142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29813 (p : Pattern) (ha : d147927 p = 1) (hb : d152143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d152130 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d152131 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147916 q = 1) (hb : d152132 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147916, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147916, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147927 q = 1) (hb : d152143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147927, d152143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147927, d152143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29814 (p : Pattern) (ha : d147933 p = 1) (hb : d152149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147918 q = 1) (hb : d152134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29809 q ha hb
    | true =>
      simp only [d147918, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29810 q ha hb
  have h2 (q : Pattern) (ha : d147919 q = 1) (hb : d152135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147919, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147919, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147920 q = 1) (hb : d152136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147920, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147920, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147921 q = 1) (hb : d152137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147921, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147921, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147922 q = 1) (hb : d152138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147922, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147922, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147928 q = 1) (hb : d152144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29812 q ha hb
    | true =>
      simp only [d147928, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29813 q ha hb
  have h7 (q : Pattern) (ha : d147929 q = 1) (hb : d152145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147929, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147929, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147930 q = 1) (hb : d152146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147930, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147930, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147931 q = 1) (hb : d152147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147931, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147931, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147932 q = 1) (hb : d152148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147932, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147932, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147933 q = 1) (hb : d152149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147933, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147933, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29815 (p : Pattern) (ha : d147938 p = 1) (hb : d152154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d152120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29807 q ha hb
    | true =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d152121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d152126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d152127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147937 q = 1) (hb : d152153 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147937, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147937, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147938 q = 1) (hb : d152154 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147938, d152154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147938, d152154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29816 (p : Pattern) (ha : d147940 p = 1) (hb : d152156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d152130 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d152131 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147939 q = 1) (hb : d152155 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147939, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147939, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147940 q = 1) (hb : d152156 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147940, d152156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147940, d152156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29817 (p : Pattern) (ha : d147947 p = 1) (hb : d152163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d152120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29807 q ha hb
    | true =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d152121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d152126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147945 q = 1) (hb : d152161 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147945, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147945, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147946 q = 1) (hb : d152162 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147946, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147946, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147947 q = 1) (hb : d152163 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147947, d152163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147947, d152163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29818 (p : Pattern) (ha : d147950 p = 1) (hb : d152166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d152130 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147948 q = 1) (hb : d152164 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147948, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147948, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147949 q = 1) (hb : d152165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147949, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147949, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147950 q = 1) (hb : d152166 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147950, d152166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147950, d152166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29819 (p : Pattern) (ha : d13350 p = 1) (hb : d113610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10057 q = 1) (hb : d101484 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7963 q ha hb
    | true =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10058 q = 1) (hb : d101485 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10080 q = 1) (hb : d101507 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10080, d101507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10080, d101507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1549 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1550 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10081 q = 1) (hb : d101508 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10081, d101508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10081, d101508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10082 q = 1) (hb : d101509 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10082, d101509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10082, d101509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10083 q = 1) (hb : d101510 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10083, d101510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10083, d101510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d13350 q = 1) (hb : d113610 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13350, d113610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13350, d113610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h12 p ha hb
theorem andIntro29820 (p : Pattern) (ha : d22323 p = 1) (hb : d147965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h5 (q : Pattern) (ha : d10056 q = 1) (hb : d101483 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10095 q = 1) (hb : d101522 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10095, d101522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10095, d101522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10096 q = 1) (hb : d101523 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10096, d101523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10096, d101523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10097 q = 1) (hb : d101524 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10097, d101524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10097, d101524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d22323 q = 1) (hb : d147965 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22323, d147965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22323, d147965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h9 p ha hb
theorem andIntro29821 (p : Pattern) (ha : d147971 p = 1) (hb : d152173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22324 q = 1) (hb : d147966 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22324, d147966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29820 q ha hb
    | true =>
      simp only [d22324, d147966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22325 q = 1) (hb : d147967 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22325, d147967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22325, d147967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22326 q = 1) (hb : d147968 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22326, d147968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22326, d147968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22327 q = 1) (hb : d147969 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22327, d147969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22327, d147969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13353 q = 1) (hb : d113613 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13354 q = 1) (hb : d113614 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22328 q = 1) (hb : d147970 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22328, d147970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22328, d147970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147880 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d147971 q = 1) (hb : d152173 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147971, d152173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147971, d152173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro29822 (p : Pattern) (ha : d147977 p = 1) (hb : d152179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147962 q = 1) (hb : d152170 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147962, d152170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28262 q ha hb
    | true =>
      simp only [d147962, d152170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28246 q ha hb
  have h2 (q : Pattern) (ha : d147963 q = 1) (hb : d152171 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147963, d152171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147963, d152171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147964 q = 1) (hb : d152172 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147964, d152172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147964, d152172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147972 q = 1) (hb : d152174 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147972, d152174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28246 q ha hb
    | true =>
      simp only [d147972, d152174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29821 q ha hb
  have h5 (q : Pattern) (ha : d147973 q = 1) (hb : d152175 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147973, d152175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147973, d152175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147974 q = 1) (hb : d152176 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147974, d152176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147974, d152176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147975 q = 1) (hb : d152177 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147975, d152177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147975, d152177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147882 q = 1) (hb : d152106 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28246 q ha hb
    | true =>
      simp only [d147882, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
  have h9 (q : Pattern) (ha : d147883 q = 1) (hb : d152107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147884 q = 1) (hb : d152108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147892 q = 1) (hb : d152110 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147892, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29806 q ha hb
  have h12 (q : Pattern) (ha : d147893 q = 1) (hb : d152111 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147894 q = 1) (hb : d152112 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147895 q = 1) (hb : d152113 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147895, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147976 q = 1) (hb : d152178 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147976, d152178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147976, d152178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147977 q = 1) (hb : d152179 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147977, d152179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147977, d152179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro29823 (p : Pattern) (ha : d147982 p = 1) (hb : d152184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147882 q = 1) (hb : d152106 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28246 q ha hb
    | true =>
      simp only [d147882, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
  have h2 (q : Pattern) (ha : d147883 q = 1) (hb : d152107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147884 q = 1) (hb : d152108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147892 q = 1) (hb : d152110 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147892, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29806 q ha hb
  have h5 (q : Pattern) (ha : d147893 q = 1) (hb : d152111 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147894 q = 1) (hb : d152112 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147895 q = 1) (hb : d152113 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147895, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147980 q = 1) (hb : d152182 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147980, d152182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147980, d152182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147981 q = 1) (hb : d152183 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147981, d152183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147981, d152183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147982 q = 1) (hb : d152184 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147982, d152184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147982, d152184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29824 (p : Pattern) (ha : d147988 p = 1) (hb : d152190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147978 q = 1) (hb : d152180 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147978, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29822 q ha hb
    | true =>
      simp only [d147978, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147979 q = 1) (hb : d152181 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147979, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147979, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147983 q = 1) (hb : d152185 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29823 q ha hb
    | true =>
      simp only [d147983, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147984 q = 1) (hb : d152186 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147985 q = 1) (hb : d152187 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147985, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147985, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147986 q = 1) (hb : d152188 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147986, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147986, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147987 q = 1) (hb : d152189 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147987, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147987, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147988 q = 1) (hb : d152190 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147988, d152190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147988, d152190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29825 (p : Pattern) (ha : d147992 p = 1) (hb : d152194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147983 q = 1) (hb : d152185 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29823 q ha hb
    | true =>
      simp only [d147983, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147984 q = 1) (hb : d152186 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147989 q = 1) (hb : d152191 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147989, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147989, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147990 q = 1) (hb : d152192 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147990, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147990, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147991 q = 1) (hb : d152193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147991, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147991, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147992 q = 1) (hb : d152194 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147992, d152194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147992, d152194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29826 (p : Pattern) (ha : d22421 p = 1) (hb : d147995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22233 q = 1) (hb : d147875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
    | true =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22234 q = 1) (hb : d147876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22235 q = 1) (hb : d147877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22235, d147877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22235, d147877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22236 q = 1) (hb : d147878 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22236, d147878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22236, d147878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22254 q = 1) (hb : d147896 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22254, d147896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22254, d147896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22421 q = 1) (hb : d147995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22421, d147995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22421, d147995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29827 (p : Pattern) (ha : d148001 p = 1) (hb : d152119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147882 q = 1) (hb : d152106 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28246 q ha hb
    | true =>
      simp only [d147882, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
  have h2 (q : Pattern) (ha : d147883 q = 1) (hb : d152107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147884 q = 1) (hb : d152108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147892 q = 1) (hb : d152110 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147892, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29806 q ha hb
  have h5 (q : Pattern) (ha : d147893 q = 1) (hb : d152111 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147894 q = 1) (hb : d152112 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147895 q = 1) (hb : d152113 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147895, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147996 q = 1) (hb : d152114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147996, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28248 q ha hb
    | true =>
      simp only [d147996, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29826 q hb ha
  have h9 (q : Pattern) (ha : d147997 q = 1) (hb : d152115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147997, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147997, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147998 q = 1) (hb : d152116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147998, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147998, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147999 q = 1) (hb : d152117 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147999, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147999, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148000 q = 1) (hb : d152118 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148000, d152118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148000, d152118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148001 q = 1) (hb : d152119 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148001, d152119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148001, d152119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29828 (p : Pattern) (ha : d148007 p = 1) (hb : d152200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148002 q = 1) (hb : d152120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148002, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29827 q ha hb
    | true =>
      simp only [d148002, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148003 q = 1) (hb : d152121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148003, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148003, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148004 q = 1) (hb : d152197 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148004, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148004, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148005 q = 1) (hb : d152198 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148005, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148005, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148006 q = 1) (hb : d152199 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148006, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148006, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148007 q = 1) (hb : d152200 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148007, d152200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148007, d152200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29829 (p : Pattern) (ha : d148013 p = 1) (hb : d152206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147941 q = 1) (hb : d152157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147941, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29815 q ha hb
    | true =>
      simp only [d147941, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29816 q ha hb
  have h2 (q : Pattern) (ha : d147942 q = 1) (hb : d152158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147942, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147942, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147943 q = 1) (hb : d152159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147943, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147943, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147944 q = 1) (hb : d152160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147944, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147944, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147951 q = 1) (hb : d152167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147951, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29817 q ha hb
    | true =>
      simp only [d147951, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29818 q ha hb
  have h6 (q : Pattern) (ha : d147952 q = 1) (hb : d152168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147952, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147952, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147953 q = 1) (hb : d152169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147953, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147953, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147993 q = 1) (hb : d152195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147993, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29824 q ha hb
    | true =>
      simp only [d147993, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29825 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147918 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147994 q = 1) (hb : d152196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147994, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148008 q = 1) (hb : d152201 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148008, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29828 q ha hb
    | true =>
      simp only [d148008, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148009 q = 1) (hb : d152202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148009, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148009, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148010 q = 1) (hb : d152203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148010, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148011 q = 1) (hb : d152204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148011, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148012 q = 1) (hb : d152205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148012, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148013 q = 1) (hb : d152206 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148013, d152206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148013, d152206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro29830 (p : Pattern) (ha : d148014 p = 1) (hb : d152207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d152120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29807 q ha hb
    | true =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d152121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d152126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d152127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147937 q = 1) (hb : d152153 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147937, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147937, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148014 q = 1) (hb : d152207 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148014, d152207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148014, d152207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29831 (p : Pattern) (ha : d148015 p = 1) (hb : d152208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d152130 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d152131 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147939 q = 1) (hb : d152155 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147939, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147939, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148015 q = 1) (hb : d152208 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148015, d152208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148015, d152208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29832 (p : Pattern) (ha : d148020 p = 1) (hb : d152213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d152120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29807 q ha hb
    | true =>
      simp only [d147904, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d152121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d152126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147945 q = 1) (hb : d152161 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147945, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147945, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147946 q = 1) (hb : d152162 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147946, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147946, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148020 q = 1) (hb : d152213 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148020, d152213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148020, d152213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29833 (p : Pattern) (ha : d148021 p = 1) (hb : d152214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d152130 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147948 q = 1) (hb : d152164 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147948, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147948, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147949 q = 1) (hb : d152165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147949, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147949, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148021 q = 1) (hb : d152214 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148021, d152214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148021, d152214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29834 (p : Pattern) (ha : d148025 p = 1) (hb : d152218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147978 q = 1) (hb : d152180 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147978, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29822 q ha hb
    | true =>
      simp only [d147978, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147979 q = 1) (hb : d152181 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147979, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147979, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147983 q = 1) (hb : d152185 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29823 q ha hb
    | true =>
      simp only [d147983, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147984 q = 1) (hb : d152186 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147985 q = 1) (hb : d152187 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147985, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147985, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147986 q = 1) (hb : d152188 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147986, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147986, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147987 q = 1) (hb : d152189 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147987, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147987, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148025 q = 1) (hb : d152218 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148025, d152218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148025, d152218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29835 (p : Pattern) (ha : d148026 p = 1) (hb : d152219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147983 q = 1) (hb : d152185 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29823 q ha hb
    | true =>
      simp only [d147983, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147984 q = 1) (hb : d152186 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d152124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29808 q ha hb
    | true =>
      simp only [d147908, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d152125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147989 q = 1) (hb : d152191 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147989, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147989, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147990 q = 1) (hb : d152192 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147990, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147990, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147991 q = 1) (hb : d152193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147991, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147991, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148026 q = 1) (hb : d152219 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148026, d152219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148026, d152219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29836 (p : Pattern) (ha : d148029 p = 1) (hb : d152222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148002 q = 1) (hb : d152120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148002, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29827 q ha hb
    | true =>
      simp only [d148002, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148003 q = 1) (hb : d152121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148003, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148003, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148004 q = 1) (hb : d152197 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148004, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148004, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148005 q = 1) (hb : d152198 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148005, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148005, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148006 q = 1) (hb : d152199 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148006, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148006, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148029 q = 1) (hb : d152222 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148029, d152222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148029, d152222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29837 (p : Pattern) (ha : d148035 p = 1) (hb : d152228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147941 q = 1) (hb : d152157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147941, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29815 q ha hb
    | true =>
      simp only [d147941, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29816 q ha hb
  have h2 (q : Pattern) (ha : d147942 q = 1) (hb : d152158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147942, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147942, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147943 q = 1) (hb : d152159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147943, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147943, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147944 q = 1) (hb : d152160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147944, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147944, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147951 q = 1) (hb : d152167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147951, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29817 q ha hb
    | true =>
      simp only [d147951, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29818 q ha hb
  have h6 (q : Pattern) (ha : d147952 q = 1) (hb : d152168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147952, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147952, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147953 q = 1) (hb : d152169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147953, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147953, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147993 q = 1) (hb : d152195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147993, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29824 q ha hb
    | true =>
      simp only [d147993, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29825 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147918 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147994 q = 1) (hb : d152196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147994, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148008 q = 1) (hb : d152201 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148008, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29828 q ha hb
    | true =>
      simp only [d148008, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148009 q = 1) (hb : d152202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148009, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148009, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148010 q = 1) (hb : d152203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148010, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148011 q = 1) (hb : d152204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148011, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148012 q = 1) (hb : d152205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148012, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148016 q = 1) (hb : d152209 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148016, d152209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29830 q ha hb
    | true =>
      simp only [d148016, d152209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29831 q ha hb
  have h17 (q : Pattern) (ha : d148017 q = 1) (hb : d152210 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148017, d152210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148017, d152210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148018 q = 1) (hb : d152211 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148018, d152211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148018, d152211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d148019 q = 1) (hb : d152212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148019, d152212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148019, d152212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148022 q = 1) (hb : d152215 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148022, d152215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29832 q ha hb
    | true =>
      simp only [d148022, d152215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29833 q ha hb
  have h21 (q : Pattern) (ha : d148023 q = 1) (hb : d152216 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148023, d152216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148023, d152216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d148024 q = 1) (hb : d152217 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148024, d152217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148024, d152217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148027 q = 1) (hb : d152220 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148027, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29834 q ha hb
    | true =>
      simp only [d148027, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29835 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d147928 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d148028 q = 1) (hb : d152221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d148028, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d148030 q = 1) (hb : d152223 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148030, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29836 q ha hb
    | true =>
      simp only [d148030, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d148031 q = 1) (hb : d152224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148031, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d148031, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d148032 q = 1) (hb : d152225 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d148032, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d148033 q = 1) (hb : d152226 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148033, d152226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d148033, d152226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d148034 q = 1) (hb : d152227 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148034, d152227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148034, d152227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d148035 q = 1) (hb : d152228 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148035, d152228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148035, d152228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro29838 (p : Pattern) (ha : d148047 p = 1) (hb : d152240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148037 q = 1) (hb : d152230 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148037, d152230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29825 q ha hb
    | true =>
      simp only [d148037, d152230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29810 q ha hb
  have h2 (q : Pattern) (ha : d148038 q = 1) (hb : d152231 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148038, d152231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148038, d152231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148039 q = 1) (hb : d152232 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148039, d152232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148039, d152232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148040 q = 1) (hb : d152233 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148040, d152233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148040, d152233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148041 q = 1) (hb : d152234 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148041, d152234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148041, d152234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148042 q = 1) (hb : d152235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148042, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29810 q ha hb
    | true =>
      simp only [d148042, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148043 q = 1) (hb : d152236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148043, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148043, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148044 q = 1) (hb : d152237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148044, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148044, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148045 q = 1) (hb : d152238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148045, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148045, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148046 q = 1) (hb : d152239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148046, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148046, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148047 q = 1) (hb : d152240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148047, d152240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148047, d152240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29839 (p : Pattern) (ha : d148053 p = 1) (hb : d152246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148042 q = 1) (hb : d152235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148042, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29810 q ha hb
    | true =>
      simp only [d148042, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148043 q = 1) (hb : d152236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148043, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148043, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148044 q = 1) (hb : d152237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148044, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148044, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148045 q = 1) (hb : d152238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148045, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148045, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148046 q = 1) (hb : d152239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148046, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148046, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148048 q = 1) (hb : d152241 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148048, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29813 q ha hb
    | true =>
      simp only [d148048, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148049 q = 1) (hb : d152242 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148049, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148049, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148050 q = 1) (hb : d152243 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148050, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148050, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148051 q = 1) (hb : d152244 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148051, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148051, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148052 q = 1) (hb : d152245 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148052, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148052, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148053 q = 1) (hb : d152246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148053, d152246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148053, d152246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29840 (p : Pattern) (ha : d148060 p = 1) (hb : d152253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148027 q = 1) (hb : d152220 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148027, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29834 q ha hb
    | true =>
      simp only [d148027, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29835 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147928 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148028 q = 1) (hb : d152221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148028, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148030 q = 1) (hb : d152223 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148030, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29836 q ha hb
    | true =>
      simp only [d148030, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148031 q = 1) (hb : d152224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148031, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148031, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148032 q = 1) (hb : d152225 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148032, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148058 q = 1) (hb : d152251 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148058, d152251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148058, d152251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148059 q = 1) (hb : d152252 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148059, d152252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148059, d152252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148060 q = 1) (hb : d152253 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148060, d152253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148060, d152253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29841 (p : Pattern) (ha : d148062 p = 1) (hb : d152255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148048 q = 1) (hb : d152241 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148048, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29813 q ha hb
    | true =>
      simp only [d148048, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148049 q = 1) (hb : d152242 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148049, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148049, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148050 q = 1) (hb : d152243 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148050, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148050, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148051 q = 1) (hb : d152244 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148051, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148051, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148052 q = 1) (hb : d152245 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148052, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148052, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148062 q = 1) (hb : d152255 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148062, d152255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148062, d152255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29842 (p : Pattern) (ha : d148095 p = 1) (hb : d152264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22518 q = 1) (hb : d148089 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22518, d148089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22518, d148089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29820 q ha hb
  have h2 (q : Pattern) (ha : d22324 q = 1) (hb : d147966 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22324, d147966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29820 q ha hb
    | true =>
      simp only [d22324, d147966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22519 q = 1) (hb : d148090 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22519, d148090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22519, d148090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22325 q = 1) (hb : d147967 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22325, d147967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22325, d147967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22520 q = 1) (hb : d148091 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22520, d148091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22520, d148091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22521 q = 1) (hb : d148092 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22521, d148092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22521, d148092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13490 q = 1) (hb : d113712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
  have h8 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13491 q = 1) (hb : d113713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13492 q = 1) (hb : d113714 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13493 q = 1) (hb : d113715 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22522 q = 1) (hb : d148093 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22522, d148093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22522, d148093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148094 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148095 q = 1) (hb : d152264 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148095, d152264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d148095, d152264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro29843 (p : Pattern) (ha : d148114 p = 1) (hb : d152272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22538 q = 1) (hb : d148109 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22538, d148109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22538, d148109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29805 q ha hb
  have h2 (q : Pattern) (ha : d22244 q = 1) (hb : d147886 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22244, d147886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29805 q ha hb
    | true =>
      simp only [d22244, d147886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22539 q = 1) (hb : d148110 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22539, d148110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22539, d148110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22245 q = 1) (hb : d147887 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22245, d147887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22245, d147887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22540 q = 1) (hb : d148111 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22540, d148111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22540, d148111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22541 q = 1) (hb : d148112 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22541, d148112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22541, d148112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22542 q = 1) (hb : d148113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22542, d148113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22542, d148113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148114 q = 1) (hb : d152272 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148114, d152272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d148114, d152272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro29844 (p : Pattern) (ha : d148120 p = 1) (hb : d152278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148086 q = 1) (hb : d152261 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148086, d152261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28282 q ha hb
    | true =>
      simp only [d148086, d152261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
  have h2 (q : Pattern) (ha : d148087 q = 1) (hb : d152262 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148087, d152262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148087, d152262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148088 q = 1) (hb : d152263 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148088, d152263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148088, d152263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148096 q = 1) (hb : d152265 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148096, d152265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
    | true =>
      simp only [d148096, d152265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29842 q ha hb
  have h5 (q : Pattern) (ha : d148097 q = 1) (hb : d152266 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148097, d152266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148097, d152266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148098 q = 1) (hb : d152267 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148098, d152267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148098, d152267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148099 q = 1) (hb : d152268 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148099, d152268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148099, d152268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148106 q = 1) (hb : d152269 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
    | true =>
      simp only [d148106, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
  have h9 (q : Pattern) (ha : d148107 q = 1) (hb : d152270 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148108 q = 1) (hb : d152271 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148115 q = 1) (hb : d152273 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148115, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29843 q ha hb
  have h12 (q : Pattern) (ha : d148116 q = 1) (hb : d152274 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148117 q = 1) (hb : d152275 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148118 q = 1) (hb : d152276 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148118, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148119 q = 1) (hb : d152277 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148119, d152277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148119, d152277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148120 q = 1) (hb : d152278 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148120, d152278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148120, d152278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro29845 (p : Pattern) (ha : d148125 p = 1) (hb : d152283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148106 q = 1) (hb : d152269 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
    | true =>
      simp only [d148106, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
  have h2 (q : Pattern) (ha : d148107 q = 1) (hb : d152270 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148108 q = 1) (hb : d152271 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148115 q = 1) (hb : d152273 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148115, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29843 q ha hb
  have h5 (q : Pattern) (ha : d148116 q = 1) (hb : d152274 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148117 q = 1) (hb : d152275 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148118 q = 1) (hb : d152276 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148118, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148123 q = 1) (hb : d152281 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148123, d152281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148123, d152281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148124 q = 1) (hb : d152282 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148124, d152282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148124, d152282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148125 q = 1) (hb : d152283 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148125, d152283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148125, d152283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29846 (p : Pattern) (ha : d148131 p = 1) (hb : d152289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148121 q = 1) (hb : d152279 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148121, d152279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29844 q ha hb
    | true =>
      simp only [d148121, d152279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148122 q = 1) (hb : d152280 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148122, d152280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148122, d152280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148126 q = 1) (hb : d152284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148126, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29845 q ha hb
    | true =>
      simp only [d148126, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148127 q = 1) (hb : d152285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148127, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148127, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148128 q = 1) (hb : d152286 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148128, d152286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148128, d152286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148129 q = 1) (hb : d152287 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148129, d152287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148129, d152287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148130 q = 1) (hb : d152288 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148130, d152288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148130, d152288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148131 q = 1) (hb : d152289 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148131, d152289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148131, d152289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29847 (p : Pattern) (ha : d22639 p = 1) (hb : d148133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22529 q = 1) (hb : d148100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d148100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d148100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
  have h2 (q : Pattern) (ha : d22233 q = 1) (hb : d147875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
    | true =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22530 q = 1) (hb : d148101 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d148101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22530, d148101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22234 q = 1) (hb : d147876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22531 q = 1) (hb : d148102 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d148102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22531, d148102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22532 q = 1) (hb : d148103 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d148103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22532, d148103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22561 q = 1) (hb : d148132 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22561, d148132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22561, d148132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d22639 q = 1) (hb : d148133 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22639, d148133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22639, d148133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29848 (p : Pattern) (ha : d148139 p = 1) (hb : d152295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148134 q = 1) (hb : d152290 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148134, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148134, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29847 q hb ha
  have h2 (q : Pattern) (ha : d148135 q = 1) (hb : d152291 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148135, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148135, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148136 q = 1) (hb : d152292 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148136, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148136, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148137 q = 1) (hb : d152293 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148137, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148137, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148138 q = 1) (hb : d152294 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148138, d152294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148138, d152294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148139 q = 1) (hb : d152295 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148139, d152295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148139, d152295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29849 (p : Pattern) (ha : d148145 p = 1) (hb : d152301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148126 q = 1) (hb : d152284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148126, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29845 q ha hb
    | true =>
      simp only [d148126, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148127 q = 1) (hb : d152285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148127, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148127, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148140 q = 1) (hb : d152296 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29848 q ha hb
    | true =>
      simp only [d148140, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148141 q = 1) (hb : d152297 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148142 q = 1) (hb : d152298 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148142, d152298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148142, d152298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148143 q = 1) (hb : d152299 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148143, d152299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148143, d152299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148144 q = 1) (hb : d152300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148144, d152300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148144, d152300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148145 q = 1) (hb : d152301 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148145, d152301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148145, d152301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29850 (p : Pattern) (ha : d22639 p = 1) (hb : d148161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22529 q = 1) (hb : d148100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d148100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d148100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
  have h2 (q : Pattern) (ha : d22233 q = 1) (hb : d147875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
    | true =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22530 q = 1) (hb : d148101 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d148101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22530, d148101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22234 q = 1) (hb : d147876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22531 q = 1) (hb : d148102 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d148102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22531, d148102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22532 q = 1) (hb : d148103 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d148103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22532, d148103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22561 q = 1) (hb : d148132 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22561, d148132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22561, d148132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22639 q = 1) (hb : d148161 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22639, d148161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22639, d148161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29851 (p : Pattern) (ha : d148167 p = 1) (hb : d152305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148106 q = 1) (hb : d152269 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
    | true =>
      simp only [d148106, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
  have h2 (q : Pattern) (ha : d148107 q = 1) (hb : d152270 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148108 q = 1) (hb : d152271 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148115 q = 1) (hb : d152273 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148115, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29843 q ha hb
  have h5 (q : Pattern) (ha : d148116 q = 1) (hb : d152274 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148117 q = 1) (hb : d152275 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148118 q = 1) (hb : d152276 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148118, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148162 q = 1) (hb : d152290 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148162, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148162, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29850 q hb ha
  have h9 (q : Pattern) (ha : d148163 q = 1) (hb : d152291 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148163, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148163, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148164 q = 1) (hb : d152292 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148164, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148164, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148165 q = 1) (hb : d152293 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148165, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148165, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148166 q = 1) (hb : d152304 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148166, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148166, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148167 q = 1) (hb : d152305 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148167, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148167, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29852 (p : Pattern) (ha : d148173 p = 1) (hb : d152311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148168 q = 1) (hb : d152306 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148168, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29851 q ha hb
    | true =>
      simp only [d148168, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148169 q = 1) (hb : d152307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148169, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148169, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148170 q = 1) (hb : d152308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148170, d152308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148170, d152308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148171 q = 1) (hb : d152309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148171, d152309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148171, d152309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148172 q = 1) (hb : d152310 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148172, d152310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148172, d152310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148173 q = 1) (hb : d152311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148173, d152311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148173, d152311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29853 (p : Pattern) (ha : d148179 p = 1) (hb : d152317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148146 q = 1) (hb : d152302 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148146, d152302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29846 q ha hb
    | true =>
      simp only [d148146, d152302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29849 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148159 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148160 q = 1) (hb : d152303 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148160, d152303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148160, d152303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148174 q = 1) (hb : d152312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148174, d152312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29852 q ha hb
    | true =>
      simp only [d148174, d152312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148175 q = 1) (hb : d152313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148175, d152313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148175, d152313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148176 q = 1) (hb : d152314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148176, d152314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148176, d152314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148177 q = 1) (hb : d152315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148177, d152315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148177, d152315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148178 q = 1) (hb : d152316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148178, d152316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148178, d152316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148179 q = 1) (hb : d152317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148179, d152317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148179, d152317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29854 (p : Pattern) (ha : d148158 p = 1) (hb : d152322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148140 q = 1) (hb : d152296 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29848 q ha hb
    | true =>
      simp only [d148140, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148141 q = 1) (hb : d152297 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148155 q = 1) (hb : d152319 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148155, d152319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148155, d152319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148156 q = 1) (hb : d152320 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148156, d152320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148156, d152320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148157 q = 1) (hb : d152321 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148157, d152321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148157, d152321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148158 q = 1) (hb : d152322 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148158, d152322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148158, d152322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29855 (p : Pattern) (ha : d148186 p = 1) (hb : d152328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148181 q = 1) (hb : d152323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148181, d152323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29854 q ha hb
    | true =>
      simp only [d148181, d152323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148182 q = 1) (hb : d152324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148182, d152324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148182, d152324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148183 q = 1) (hb : d152325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148183, d152325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148183, d152325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148184 q = 1) (hb : d152326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148184, d152326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148184, d152326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148185 q = 1) (hb : d152327 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148185, d152327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148185, d152327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148186 q = 1) (hb : d152328 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148186, d152328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148186, d152328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29856 (p : Pattern) (ha : d148192 p = 1) (hb : d152334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147924 q = 1) (hb : d152140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147924, d152140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147924, d152140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29811 q ha hb
  have h2 (q : Pattern) (ha : d147925 q = 1) (hb : d152141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147925, d152141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147925, d152141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d147934 q = 1) (hb : d152150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147934, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29811 q ha hb
    | true =>
      simp only [d147934, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29814 q ha hb
  have h4 (q : Pattern) (ha : d147935 q = 1) (hb : d152151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147935, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147935, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147936 q = 1) (hb : d152152 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147936, d152152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147936, d152152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148036 q = 1) (hb : d152229 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148036, d152229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29829 q ha hb
    | true =>
      simp only [d148036, d152229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29837 q ha hb
  have h7 (q : Pattern) (ha : d148054 q = 1) (hb : d152247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148054, d152247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29838 q ha hb
    | true =>
      simp only [d148054, d152247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29839 q ha hb
  have h8 (q : Pattern) (ha : d148055 q = 1) (hb : d152248 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148055, d152248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148055, d152248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148056 q = 1) (hb : d152249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148056, d152249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148056, d152249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d148057 q = 1) (hb : d152250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148057, d152250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148057, d152250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148061 q = 1) (hb : d152254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148061, d152254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148061, d152254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29840 q ha hb
  have h12 (q : Pattern) (ha : d148063 q = 1) (hb : d152256 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148063, d152256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148063, d152256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29841 q ha hb
  have h13 (q : Pattern) (ha : d148064 q = 1) (hb : d152257 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148064, d152257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148064, d152257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148065 q = 1) (hb : d152258 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148065, d152258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148065, d152258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148066 q = 1) (hb : d152259 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148066, d152259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d148066, d152259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d148067 q = 1) (hb : d152260 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148067, d152260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148067, d152260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148180 q = 1) (hb : d152318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148180, d152318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148180, d152318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29853 q ha hb
  have h18 (q : Pattern) (ha : d148187 q = 1) (hb : d152329 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148187, d152329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148187, d152329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29855 q ha hb
  have h19 (q : Pattern) (ha : d148188 q = 1) (hb : d152330 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148188, d152330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148188, d152330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148189 q = 1) (hb : d152331 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148189, d152331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148189, d152331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d148190 q = 1) (hb : d152332 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148190, d152332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d148190, d152332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d148191 q = 1) (hb : d152333 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148191, d152333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148191, d152333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148192 q = 1) (hb : d152334 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148192, d152334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148192, d152334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29857 (p : Pattern) (ha : d148198 p = 1) (hb : d152340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148193 q = 1) (hb : d152335 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148193, d152335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148193, d152335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29856 q ha hb
  have h2 (q : Pattern) (ha : d148194 q = 1) (hb : d152336 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148194, d152336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148194, d152336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148195 q = 1) (hb : d152337 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148195, d152337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148195, d152337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148196 q = 1) (hb : d152338 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148196, d152338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148196, d152338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148197 q = 1) (hb : d152339 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148197, d152339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148197, d152339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148198 q = 1) (hb : d152340 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148198, d152340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148198, d152340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29858 (p : Pattern) (ha : d22854 p = 1) (hb : d148228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22688 q = 1) (hb : d148206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
    | true =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22689 q = 1) (hb : d148207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22690 q = 1) (hb : d148208 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d148208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d148208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22691 q = 1) (hb : d148209 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d148209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22691, d148209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22709 q = 1) (hb : d148227 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22709, d148227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22709, d148227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22854 q = 1) (hb : d148228 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22854, d148228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22854, d148228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29859 (p : Pattern) (ha : d22698 p = 1) (hb : d148216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h5 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5240 q = 1) (hb : d69324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5240, d69324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5240, d69324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5241 q = 1) (hb : d69325 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5241, d69325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5241, d69325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5242 q = 1) (hb : d69326 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5242, d69326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5242, d69326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22698 q = 1) (hb : d148216 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22698, d148216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22698, d148216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h14 p ha hb
theorem andIntro29860 (p : Pattern) (ha : d148222 p = 1) (hb : d152348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22699 q = 1) (hb : d148217 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22699, d148217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29859 q ha hb
    | true =>
      simp only [d22699, d148217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22700 q = 1) (hb : d148218 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22700, d148218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22700, d148218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22701 q = 1) (hb : d148219 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22701, d148219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22701, d148219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22702 q = 1) (hb : d148220 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22702, d148220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22702, d148220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22703 q = 1) (hb : d148221 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22703, d148221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22703, d148221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148222 q = 1) (hb : d152348 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148222, d152348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d148222, d152348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro29861 (p : Pattern) (ha : d148234 p = 1) (hb : d152358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148213 q = 1) (hb : d152345 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
    | true =>
      simp only [d148213, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
  have h2 (q : Pattern) (ha : d148214 q = 1) (hb : d152346 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148215 q = 1) (hb : d152347 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148223 q = 1) (hb : d152349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148223, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29860 q ha hb
  have h5 (q : Pattern) (ha : d148224 q = 1) (hb : d152350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148225 q = 1) (hb : d152351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148226 q = 1) (hb : d152352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148226, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148229 q = 1) (hb : d152353 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148229, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148229, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29858 q hb ha
  have h9 (q : Pattern) (ha : d148230 q = 1) (hb : d152354 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148230, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148230, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148231 q = 1) (hb : d152355 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148231, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148231, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148232 q = 1) (hb : d152356 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148232, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148232, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148233 q = 1) (hb : d152357 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148233, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148233, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148234 q = 1) (hb : d152358 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148234, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148234, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29862 (p : Pattern) (ha : d148238 p = 1) (hb : d152362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148229 q = 1) (hb : d152353 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148229, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148229, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29858 q hb ha
  have h2 (q : Pattern) (ha : d148230 q = 1) (hb : d152354 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148230, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148230, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148231 q = 1) (hb : d152355 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148231, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148231, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148232 q = 1) (hb : d152356 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148232, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148232, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148237 q = 1) (hb : d152361 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148237, d152361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148237, d152361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148238 q = 1) (hb : d152362 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148238, d152362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148238, d152362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29863 (p : Pattern) (ha : d148244 p = 1) (hb : d152368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29861 q ha hb
    | true =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d152366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148243 q = 1) (hb : d152367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148243, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148243, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148244 q = 1) (hb : d152368 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148244, d152368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148244, d152368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29864 (p : Pattern) (ha : d148248 p = 1) (hb : d152372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d152370 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148247 q = 1) (hb : d152371 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148247, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148247, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148248 q = 1) (hb : d152372 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148248, d152372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148248, d152372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29865 (p : Pattern) (ha : d148254 p = 1) (hb : d152378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148249 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29863 q ha hb
    | true =>
      simp only [d148249, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29864 q ha hb
  have h2 (q : Pattern) (ha : d148250 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148250, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148250, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148251 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148251, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148251, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148252 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148252, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148252, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148253 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148253, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148253, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148254 q = 1) (hb : d152378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148254, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148254, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29866 (p : Pattern) (ha : d148257 p = 1) (hb : d152381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29861 q ha hb
    | true =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d152366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148243 q = 1) (hb : d152367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148243, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148243, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148257 q = 1) (hb : d152381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148257, d152381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148257, d152381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29867 (p : Pattern) (ha : d148258 p = 1) (hb : d152382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d152370 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148247 q = 1) (hb : d152371 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148247, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148247, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148258 q = 1) (hb : d152382 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148258, d152382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148258, d152382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29868 (p : Pattern) (ha : d148264 p = 1) (hb : d152388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148249 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29863 q ha hb
    | true =>
      simp only [d148249, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29864 q ha hb
  have h2 (q : Pattern) (ha : d148250 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148250, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148250, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148251 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148251, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148251, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148252 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148252, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148252, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148253 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148253, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148253, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148259 q = 1) (hb : d152383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29866 q ha hb
    | true =>
      simp only [d148259, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29867 q ha hb
  have h7 (q : Pattern) (ha : d148260 q = 1) (hb : d152384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148260, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148260, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148261 q = 1) (hb : d152385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148261, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148261, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148262 q = 1) (hb : d152386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148262, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148262, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148263 q = 1) (hb : d152387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148263, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148263, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148264 q = 1) (hb : d152388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148264, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148264, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29869 (p : Pattern) (ha : d148269 p = 1) (hb : d152393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29861 q ha hb
    | true =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d152366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148268 q = 1) (hb : d152392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148268, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148268, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148269 q = 1) (hb : d152393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148269, d152393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148269, d152393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29870 (p : Pattern) (ha : d148271 p = 1) (hb : d152395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d152370 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148270 q = 1) (hb : d152394 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148270, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148270, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148271 q = 1) (hb : d152395 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148271, d152395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148271, d152395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29871 (p : Pattern) (ha : d148278 p = 1) (hb : d152402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29861 q ha hb
    | true =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148276 q = 1) (hb : d152400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148276, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148276, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148277 q = 1) (hb : d152401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148277, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148277, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148278 q = 1) (hb : d152402 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148278, d152402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148278, d152402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29872 (p : Pattern) (ha : d148281 p = 1) (hb : d152405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148279 q = 1) (hb : d152403 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148279, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148279, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148280 q = 1) (hb : d152404 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148280, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148280, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148281 q = 1) (hb : d152405 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148281, d152405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148281, d152405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29873 (p : Pattern) (ha : d13677 p = 1) (hb : d113867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5715 q = 1) (hb : d74441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d5716 q = 1) (hb : d74442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5717 q = 1) (hb : d74443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d13677 q = 1) (hb : d113867 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13677, d113867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13677, d113867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro29874 (p : Pattern) (ha : d13683 p = 1) (hb : d148290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13678 q = 1) (hb : d113868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13679 q = 1) (hb : d113869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13680 q = 1) (hb : d113870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13681 q = 1) (hb : d113871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13682 q = 1) (hb : d113872 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13682, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148211 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13683 q = 1) (hb : d148290 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13683, d148290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13683, d148290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29875 (p : Pattern) (ha : d148296 p = 1) (hb : d152417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148287 q = 1) (hb : d152409 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148287, d152409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28312 q ha hb
    | true =>
      simp only [d148287, d152409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
  have h2 (q : Pattern) (ha : d148288 q = 1) (hb : d152410 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148288, d152410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148288, d152410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148289 q = 1) (hb : d152411 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148289, d152411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148289, d152411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148291 q = 1) (hb : d152412 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148291, d152412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
    | true =>
      simp only [d148291, d152412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29874 q hb ha
  have h5 (q : Pattern) (ha : d148292 q = 1) (hb : d152413 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148292, d152413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148292, d152413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148293 q = 1) (hb : d152414 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148293, d152414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148293, d152414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148294 q = 1) (hb : d152415 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148294, d152415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148294, d152415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148213 q = 1) (hb : d152345 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
    | true =>
      simp only [d148213, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
  have h9 (q : Pattern) (ha : d148214 q = 1) (hb : d152346 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148215 q = 1) (hb : d152347 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148223 q = 1) (hb : d152349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148223, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29860 q ha hb
  have h12 (q : Pattern) (ha : d148224 q = 1) (hb : d152350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148225 q = 1) (hb : d152351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148226 q = 1) (hb : d152352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148226, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148295 q = 1) (hb : d152416 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148295, d152416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148295, d152416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148296 q = 1) (hb : d152417 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148296, d152417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148296, d152417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro29876 (p : Pattern) (ha : d148301 p = 1) (hb : d152422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148213 q = 1) (hb : d152345 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
    | true =>
      simp only [d148213, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
  have h2 (q : Pattern) (ha : d148214 q = 1) (hb : d152346 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148215 q = 1) (hb : d152347 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148223 q = 1) (hb : d152349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148223, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29860 q ha hb
  have h5 (q : Pattern) (ha : d148224 q = 1) (hb : d152350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148225 q = 1) (hb : d152351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148226 q = 1) (hb : d152352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148226, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148299 q = 1) (hb : d152420 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148299, d152420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148299, d152420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148300 q = 1) (hb : d152421 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148300, d152421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148300, d152421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148301 q = 1) (hb : d152422 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148301, d152422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148301, d152422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29877 (p : Pattern) (ha : d148307 p = 1) (hb : d152428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148297 q = 1) (hb : d152418 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148297, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29875 q ha hb
    | true =>
      simp only [d148297, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148298 q = 1) (hb : d152419 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148298, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148298, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148302 q = 1) (hb : d152423 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29876 q ha hb
    | true =>
      simp only [d148302, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148303 q = 1) (hb : d152424 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148304 q = 1) (hb : d152425 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148304, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148304, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148305 q = 1) (hb : d152426 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148305, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148305, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148306 q = 1) (hb : d152427 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148306, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148306, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148307 q = 1) (hb : d152428 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148307, d152428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148307, d152428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29878 (p : Pattern) (ha : d148311 p = 1) (hb : d152432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148302 q = 1) (hb : d152423 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29876 q ha hb
    | true =>
      simp only [d148302, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148303 q = 1) (hb : d152424 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148308 q = 1) (hb : d152429 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148308, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148308, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148309 q = 1) (hb : d152430 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148309, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148309, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148310 q = 1) (hb : d152431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148310, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148310, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148311 q = 1) (hb : d152432 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148311, d152432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148311, d152432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29879 (p : Pattern) (ha : d22854 p = 1) (hb : d148314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22688 q = 1) (hb : d148206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
    | true =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22689 q = 1) (hb : d148207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22690 q = 1) (hb : d148208 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d148208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d148208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22691 q = 1) (hb : d148209 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d148209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22691, d148209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22709 q = 1) (hb : d148227 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22709, d148227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22709, d148227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22854 q = 1) (hb : d148314 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22854, d148314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22854, d148314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29880 (p : Pattern) (ha : d148320 p = 1) (hb : d152358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148213 q = 1) (hb : d152345 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28297 q ha hb
    | true =>
      simp only [d148213, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
  have h2 (q : Pattern) (ha : d148214 q = 1) (hb : d152346 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148215 q = 1) (hb : d152347 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148223 q = 1) (hb : d152349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148223, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29860 q ha hb
  have h5 (q : Pattern) (ha : d148224 q = 1) (hb : d152350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148225 q = 1) (hb : d152351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148226 q = 1) (hb : d152352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148226, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148315 q = 1) (hb : d152353 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148315, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28299 q ha hb
    | true =>
      simp only [d148315, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29879 q hb ha
  have h9 (q : Pattern) (ha : d148316 q = 1) (hb : d152354 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148316, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148316, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148317 q = 1) (hb : d152355 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148317, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148317, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148318 q = 1) (hb : d152356 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148318, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148318, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148319 q = 1) (hb : d152357 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148319, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148319, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148320 q = 1) (hb : d152358 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148320, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148320, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29881 (p : Pattern) (ha : d148326 p = 1) (hb : d152438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148321 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148321, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29880 q ha hb
    | true =>
      simp only [d148321, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148322 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148322, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148322, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148323 q = 1) (hb : d152435 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148323, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148323, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148324 q = 1) (hb : d152436 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148324, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148324, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148325 q = 1) (hb : d152437 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148325, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148325, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148326 q = 1) (hb : d152438 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148326, d152438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148326, d152438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29882 (p : Pattern) (ha : d148332 p = 1) (hb : d152444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148272 q = 1) (hb : d152396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148272, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29869 q ha hb
    | true =>
      simp only [d148272, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29870 q ha hb
  have h2 (q : Pattern) (ha : d148273 q = 1) (hb : d152397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148273, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148273, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148274 q = 1) (hb : d152398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148274, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148274, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148275 q = 1) (hb : d152399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148275, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148275, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148282 q = 1) (hb : d152406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148282, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29871 q ha hb
    | true =>
      simp only [d148282, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29872 q ha hb
  have h6 (q : Pattern) (ha : d148283 q = 1) (hb : d152407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148283, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148283, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148284 q = 1) (hb : d152408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148284, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148284, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148312 q = 1) (hb : d152433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148312, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29877 q ha hb
    | true =>
      simp only [d148312, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29878 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148249 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148313 q = 1) (hb : d152434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148313, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148327 q = 1) (hb : d152439 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148327, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29881 q ha hb
    | true =>
      simp only [d148327, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148328 q = 1) (hb : d152440 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148328, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148328, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148329 q = 1) (hb : d152441 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148329, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148330 q = 1) (hb : d152442 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148330, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148331 q = 1) (hb : d152443 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148331, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148332 q = 1) (hb : d152444 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148332, d152444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148332, d152444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro29883 (p : Pattern) (ha : d148333 p = 1) (hb : d152445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29861 q ha hb
    | true =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d152366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148268 q = 1) (hb : d152392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148268, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148268, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148333 q = 1) (hb : d152445 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148333, d152445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148333, d152445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29884 (p : Pattern) (ha : d148334 p = 1) (hb : d152446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d152370 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148270 q = 1) (hb : d152394 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148270, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148270, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148334 q = 1) (hb : d152446 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148334, d152446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148334, d152446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29885 (p : Pattern) (ha : d148339 p = 1) (hb : d152451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29861 q ha hb
    | true =>
      simp only [d148235, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148276 q = 1) (hb : d152400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148276, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148276, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148277 q = 1) (hb : d152401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148277, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148277, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148339 q = 1) (hb : d152451 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148339, d152451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148339, d152451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29886 (p : Pattern) (ha : d148340 p = 1) (hb : d152452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148279 q = 1) (hb : d152403 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148279, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148279, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148280 q = 1) (hb : d152404 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148280, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148280, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148340 q = 1) (hb : d152452 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148340, d152452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148340, d152452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29887 (p : Pattern) (ha : d148344 p = 1) (hb : d152456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148297 q = 1) (hb : d152418 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148297, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29875 q ha hb
    | true =>
      simp only [d148297, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148298 q = 1) (hb : d152419 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148298, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148298, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148302 q = 1) (hb : d152423 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29876 q ha hb
    | true =>
      simp only [d148302, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148303 q = 1) (hb : d152424 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148304 q = 1) (hb : d152425 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148304, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148304, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148305 q = 1) (hb : d152426 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148305, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148305, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148306 q = 1) (hb : d152427 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148306, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148306, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148344 q = 1) (hb : d152456 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148344, d152456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148344, d152456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29888 (p : Pattern) (ha : d148345 p = 1) (hb : d152457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148302 q = 1) (hb : d152423 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29876 q ha hb
    | true =>
      simp only [d148302, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148303 q = 1) (hb : d152424 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29862 q ha hb
    | true =>
      simp only [d148239, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148308 q = 1) (hb : d152429 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148308, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148308, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148309 q = 1) (hb : d152430 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148309, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148309, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148310 q = 1) (hb : d152431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148310, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148310, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148345 q = 1) (hb : d152457 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148345, d152457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148345, d152457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29889 (p : Pattern) (ha : d148348 p = 1) (hb : d152460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148321 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148321, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29880 q ha hb
    | true =>
      simp only [d148321, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148322 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148322, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148322, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148323 q = 1) (hb : d152435 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148323, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148323, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148324 q = 1) (hb : d152436 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148324, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148324, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148325 q = 1) (hb : d152437 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148325, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148325, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148348 q = 1) (hb : d152460 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148348, d152460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148348, d152460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29890 (p : Pattern) (ha : d148354 p = 1) (hb : d152466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148272 q = 1) (hb : d152396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148272, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29869 q ha hb
    | true =>
      simp only [d148272, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29870 q ha hb
  have h2 (q : Pattern) (ha : d148273 q = 1) (hb : d152397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148273, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148273, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148274 q = 1) (hb : d152398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148274, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148274, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148275 q = 1) (hb : d152399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148275, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148275, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148282 q = 1) (hb : d152406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148282, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29871 q ha hb
    | true =>
      simp only [d148282, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29872 q ha hb
  have h6 (q : Pattern) (ha : d148283 q = 1) (hb : d152407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148283, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148283, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148284 q = 1) (hb : d152408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148284, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148284, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148312 q = 1) (hb : d152433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148312, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29877 q ha hb
    | true =>
      simp only [d148312, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29878 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148249 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148313 q = 1) (hb : d152434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148313, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148327 q = 1) (hb : d152439 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148327, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29881 q ha hb
    | true =>
      simp only [d148327, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148328 q = 1) (hb : d152440 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148328, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148328, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148329 q = 1) (hb : d152441 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148329, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148330 q = 1) (hb : d152442 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148330, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148331 q = 1) (hb : d152443 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148331, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148335 q = 1) (hb : d152447 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148335, d152447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29883 q ha hb
    | true =>
      simp only [d148335, d152447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29884 q ha hb
  have h17 (q : Pattern) (ha : d148336 q = 1) (hb : d152448 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148336, d152448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148336, d152448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148337 q = 1) (hb : d152449 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148337, d152449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148337, d152449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d148338 q = 1) (hb : d152450 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148338, d152450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148338, d152450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148341 q = 1) (hb : d152453 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148341, d152453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29885 q ha hb
    | true =>
      simp only [d148341, d152453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29886 q ha hb
  have h21 (q : Pattern) (ha : d148342 q = 1) (hb : d152454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148342, d152454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148342, d152454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d148343 q = 1) (hb : d152455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148343, d152455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148343, d152455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148346 q = 1) (hb : d152458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148346, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29887 q ha hb
    | true =>
      simp only [d148346, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29888 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d148259 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d148347 q = 1) (hb : d152459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d148347, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d148349 q = 1) (hb : d152461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148349, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29889 q ha hb
    | true =>
      simp only [d148349, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d148350 q = 1) (hb : d152462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148350, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d148350, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d148351 q = 1) (hb : d152463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d148351, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d148352 q = 1) (hb : d152464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148352, d152464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d148352, d152464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d148353 q = 1) (hb : d152465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148353, d152465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148353, d152465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d148354 q = 1) (hb : d152466 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148354, d152466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148354, d152466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro29891 (p : Pattern) (ha : d148366 p = 1) (hb : d152478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148356 q = 1) (hb : d152468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148356, d152468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29878 q ha hb
    | true =>
      simp only [d148356, d152468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29864 q ha hb
  have h2 (q : Pattern) (ha : d148357 q = 1) (hb : d152469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148357, d152469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148357, d152469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148358 q = 1) (hb : d152470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148358, d152470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148358, d152470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148359 q = 1) (hb : d152471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148359, d152471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148359, d152471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148360 q = 1) (hb : d152472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148360, d152472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148360, d152472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148361 q = 1) (hb : d152473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148361, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29864 q ha hb
    | true =>
      simp only [d148361, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148362 q = 1) (hb : d152474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148362, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148362, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148363 q = 1) (hb : d152475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148363, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148363, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148364 q = 1) (hb : d152476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148364, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148364, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148365 q = 1) (hb : d152477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148365, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148365, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148366 q = 1) (hb : d152478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148366, d152478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148366, d152478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29892 (p : Pattern) (ha : d148372 p = 1) (hb : d152484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148361 q = 1) (hb : d152473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148361, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29864 q ha hb
    | true =>
      simp only [d148361, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148362 q = 1) (hb : d152474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148362, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148362, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148363 q = 1) (hb : d152475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148363, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148363, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148364 q = 1) (hb : d152476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148364, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148364, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148365 q = 1) (hb : d152477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148365, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148365, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148367 q = 1) (hb : d152479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148367, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29867 q ha hb
    | true =>
      simp only [d148367, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148368 q = 1) (hb : d152480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148368, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148368, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148369 q = 1) (hb : d152481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148369, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148369, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148370 q = 1) (hb : d152482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148370, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148370, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148371 q = 1) (hb : d152483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148371, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148371, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148372 q = 1) (hb : d152484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148372, d152484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148372, d152484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29893 (p : Pattern) (ha : d148379 p = 1) (hb : d152491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148346 q = 1) (hb : d152458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148346, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29887 q ha hb
    | true =>
      simp only [d148346, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29888 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148259 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148347 q = 1) (hb : d152459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148347, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148349 q = 1) (hb : d152461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148349, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29889 q ha hb
    | true =>
      simp only [d148349, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148350 q = 1) (hb : d152462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148350, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148350, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148351 q = 1) (hb : d152463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148351, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148377 q = 1) (hb : d152489 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148377, d152489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148377, d152489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148378 q = 1) (hb : d152490 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148378, d152490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148378, d152490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148379 q = 1) (hb : d152491 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148379, d152491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148379, d152491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29894 (p : Pattern) (ha : d148381 p = 1) (hb : d152493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148367 q = 1) (hb : d152479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148367, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29867 q ha hb
    | true =>
      simp only [d148367, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148368 q = 1) (hb : d152480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148368, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148368, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148369 q = 1) (hb : d152481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148369, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148369, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148370 q = 1) (hb : d152482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148370, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148370, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148371 q = 1) (hb : d152483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148371, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148371, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148381 q = 1) (hb : d152493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148381, d152493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148381, d152493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29895 (p : Pattern) (ha : d13822 p = 1) (hb : d148395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13817 q = 1) (hb : d113969 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
  have h8 (q : Pattern) (ha : d13678 q = 1) (hb : d113868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13818 q = 1) (hb : d113970 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13679 q = 1) (hb : d113869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13819 q = 1) (hb : d113971 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13820 q = 1) (hb : d113972 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13821 q = 1) (hb : d113973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13821, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148394 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13822 q = 1) (hb : d148395 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13822, d148395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13822, d148395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29896 (p : Pattern) (ha : d148414 p = 1) (hb : d152509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22952 q = 1) (hb : d148409 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22952, d148409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22952, d148409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29859 q ha hb
  have h2 (q : Pattern) (ha : d22699 q = 1) (hb : d148217 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22699, d148217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29859 q ha hb
    | true =>
      simp only [d22699, d148217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22953 q = 1) (hb : d148410 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22953, d148410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22953, d148410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22700 q = 1) (hb : d148218 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22700, d148218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22700, d148218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22954 q = 1) (hb : d148411 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22954, d148411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22954, d148411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22955 q = 1) (hb : d148412 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22955, d148412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22955, d148412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22956 q = 1) (hb : d148413 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22956, d148413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22956, d148413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148414 q = 1) (hb : d152509 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148414, d152509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d148414, d152509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro29897 (p : Pattern) (ha : d148420 p = 1) (hb : d152515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148391 q = 1) (hb : d152499 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148391, d152499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28332 q ha hb
    | true =>
      simp only [d148391, d152499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
  have h2 (q : Pattern) (ha : d148392 q = 1) (hb : d152500 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148392, d152500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148392, d152500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148393 q = 1) (hb : d152501 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148393, d152501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148393, d152501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148396 q = 1) (hb : d152502 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148396, d152502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
    | true =>
      simp only [d148396, d152502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29895 q hb ha
  have h5 (q : Pattern) (ha : d148397 q = 1) (hb : d152503 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148397, d152503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148397, d152503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148398 q = 1) (hb : d152504 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148398, d152504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148398, d152504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148399 q = 1) (hb : d152505 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148399, d152505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148399, d152505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148406 q = 1) (hb : d152506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
    | true =>
      simp only [d148406, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
  have h9 (q : Pattern) (ha : d148407 q = 1) (hb : d152507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148408 q = 1) (hb : d152508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148415 q = 1) (hb : d152510 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148415, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29896 q ha hb
  have h12 (q : Pattern) (ha : d148416 q = 1) (hb : d152511 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148417 q = 1) (hb : d152512 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148418 q = 1) (hb : d152513 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148418, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148419 q = 1) (hb : d152514 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148419, d152514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148419, d152514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148420 q = 1) (hb : d152515 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148420, d152515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148420, d152515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro29898 (p : Pattern) (ha : d148425 p = 1) (hb : d152520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148406 q = 1) (hb : d152506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
    | true =>
      simp only [d148406, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
  have h2 (q : Pattern) (ha : d148407 q = 1) (hb : d152507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148408 q = 1) (hb : d152508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148415 q = 1) (hb : d152510 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148415, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29896 q ha hb
  have h5 (q : Pattern) (ha : d148416 q = 1) (hb : d152511 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148417 q = 1) (hb : d152512 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148418 q = 1) (hb : d152513 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148418, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148423 q = 1) (hb : d152518 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148423, d152518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148423, d152518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148424 q = 1) (hb : d152519 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148424, d152519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148424, d152519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148425 q = 1) (hb : d152520 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148425, d152520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148425, d152520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29899 (p : Pattern) (ha : d148431 p = 1) (hb : d152526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148421 q = 1) (hb : d152516 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148421, d152516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29897 q ha hb
    | true =>
      simp only [d148421, d152516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148422 q = 1) (hb : d152517 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148422, d152517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148422, d152517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148426 q = 1) (hb : d152521 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148426, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29898 q ha hb
    | true =>
      simp only [d148426, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148427 q = 1) (hb : d152522 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148427, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148427, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148428 q = 1) (hb : d152523 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148428, d152523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148428, d152523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148429 q = 1) (hb : d152524 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148429, d152524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148429, d152524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148430 q = 1) (hb : d152525 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148430, d152525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148430, d152525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148431 q = 1) (hb : d152526 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148431, d152526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148431, d152526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29900 (p : Pattern) (ha : d23045 p = 1) (hb : d148433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22943 q = 1) (hb : d148400 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d148400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d148400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
  have h2 (q : Pattern) (ha : d22688 q = 1) (hb : d148206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
    | true =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22944 q = 1) (hb : d148401 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d148401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22944, d148401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22689 q = 1) (hb : d148207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22945 q = 1) (hb : d148402 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d148402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22945, d148402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22946 q = 1) (hb : d148403 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d148403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22946, d148403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22975 q = 1) (hb : d148432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22975, d148432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22975, d148432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23045 q = 1) (hb : d148433 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23045, d148433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23045, d148433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29901 (p : Pattern) (ha : d148439 p = 1) (hb : d152532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148434 q = 1) (hb : d152527 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148434, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148434, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29900 q hb ha
  have h2 (q : Pattern) (ha : d148435 q = 1) (hb : d152528 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148435, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148435, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148436 q = 1) (hb : d152529 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148436, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148436, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148437 q = 1) (hb : d152530 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148437, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148437, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148438 q = 1) (hb : d152531 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148438, d152531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148438, d152531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148439 q = 1) (hb : d152532 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148439, d152532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148439, d152532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29902 (p : Pattern) (ha : d148445 p = 1) (hb : d152538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148426 q = 1) (hb : d152521 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148426, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29898 q ha hb
    | true =>
      simp only [d148426, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148427 q = 1) (hb : d152522 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148427, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148427, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148440 q = 1) (hb : d152533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29901 q ha hb
    | true =>
      simp only [d148440, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148441 q = 1) (hb : d152534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148442 q = 1) (hb : d152535 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148442, d152535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148442, d152535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148443 q = 1) (hb : d152536 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148443, d152536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148443, d152536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148444 q = 1) (hb : d152537 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148444, d152537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148444, d152537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148445 q = 1) (hb : d152538 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148445, d152538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148445, d152538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29903 (p : Pattern) (ha : d23045 p = 1) (hb : d148461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22943 q = 1) (hb : d148400 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d148400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d148400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
  have h2 (q : Pattern) (ha : d22688 q = 1) (hb : d148206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
    | true =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22944 q = 1) (hb : d148401 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d148401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22944, d148401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22689 q = 1) (hb : d148207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22945 q = 1) (hb : d148402 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d148402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22945, d148402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22946 q = 1) (hb : d148403 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d148403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22946, d148403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22975 q = 1) (hb : d148432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22975, d148432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22975, d148432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23045 q = 1) (hb : d148461 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23045, d148461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23045, d148461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29904 (p : Pattern) (ha : d148467 p = 1) (hb : d152542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148406 q = 1) (hb : d152506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
    | true =>
      simp only [d148406, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
  have h2 (q : Pattern) (ha : d148407 q = 1) (hb : d152507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148408 q = 1) (hb : d152508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148415 q = 1) (hb : d152510 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148415, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29896 q ha hb
  have h5 (q : Pattern) (ha : d148416 q = 1) (hb : d152511 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148417 q = 1) (hb : d152512 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148418 q = 1) (hb : d152513 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148418, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148462 q = 1) (hb : d152527 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148462, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148462, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29903 q hb ha
  have h9 (q : Pattern) (ha : d148463 q = 1) (hb : d152528 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148463, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148463, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148464 q = 1) (hb : d152529 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148464, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148464, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148465 q = 1) (hb : d152530 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148465, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148465, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148466 q = 1) (hb : d152541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148466, d152541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148466, d152541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148467 q = 1) (hb : d152542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148467, d152542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148467, d152542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29905 (p : Pattern) (ha : d148473 p = 1) (hb : d152548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148468 q = 1) (hb : d152543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148468, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29904 q ha hb
    | true =>
      simp only [d148468, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148469 q = 1) (hb : d152544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148469, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148469, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148470 q = 1) (hb : d152545 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148470, d152545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148470, d152545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148471 q = 1) (hb : d152546 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148471, d152546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148471, d152546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148472 q = 1) (hb : d152547 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148472, d152547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148472, d152547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148473 q = 1) (hb : d152548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148473, d152548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148473, d152548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29906 (p : Pattern) (ha : d148479 p = 1) (hb : d152554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148446 q = 1) (hb : d152539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148446, d152539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29899 q ha hb
    | true =>
      simp only [d148446, d152539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29902 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148459 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148460 q = 1) (hb : d152540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148460, d152540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148460, d152540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148474 q = 1) (hb : d152549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148474, d152549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29905 q ha hb
    | true =>
      simp only [d148474, d152549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148475 q = 1) (hb : d152550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148475, d152550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148475, d152550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148476 q = 1) (hb : d152551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148476, d152551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148476, d152551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148477 q = 1) (hb : d152552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148477, d152552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148477, d152552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148478 q = 1) (hb : d152553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148478, d152553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148478, d152553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148479 q = 1) (hb : d152554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148479, d152554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148479, d152554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29907 (p : Pattern) (ha : d148458 p = 1) (hb : d152559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148440 q = 1) (hb : d152533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29901 q ha hb
    | true =>
      simp only [d148440, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148441 q = 1) (hb : d152534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148455 q = 1) (hb : d152556 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148455, d152556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148455, d152556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148456 q = 1) (hb : d152557 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148456, d152557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148456, d152557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148457 q = 1) (hb : d152558 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148457, d152558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148457, d152558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148458 q = 1) (hb : d152559 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148458, d152559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148458, d152559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29908 (p : Pattern) (ha : d148486 p = 1) (hb : d152565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148481 q = 1) (hb : d152560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148481, d152560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29907 q ha hb
    | true =>
      simp only [d148481, d152560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148482 q = 1) (hb : d152561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148482, d152561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148482, d152561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148483 q = 1) (hb : d152562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148483, d152562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148483, d152562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148484 q = 1) (hb : d152563 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148484, d152563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148484, d152563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148485 q = 1) (hb : d152564 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148485, d152564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148485, d152564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148486 q = 1) (hb : d152565 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148486, d152565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148486, d152565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29909 (p : Pattern) (ha : d148492 p = 1) (hb : d152571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148255 q = 1) (hb : d152379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148255, d152379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148255, d152379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29865 q ha hb
  have h2 (q : Pattern) (ha : d148256 q = 1) (hb : d152380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148256, d152380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148256, d152380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148265 q = 1) (hb : d152389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148265, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29865 q ha hb
    | true =>
      simp only [d148265, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29868 q ha hb
  have h4 (q : Pattern) (ha : d148266 q = 1) (hb : d152390 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148266, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148266, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148267 q = 1) (hb : d152391 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148267, d152391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148267, d152391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148355 q = 1) (hb : d152467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148355, d152467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29882 q ha hb
    | true =>
      simp only [d148355, d152467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29890 q ha hb
  have h7 (q : Pattern) (ha : d148373 q = 1) (hb : d152485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148373, d152485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29891 q ha hb
    | true =>
      simp only [d148373, d152485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29892 q ha hb
  have h8 (q : Pattern) (ha : d148374 q = 1) (hb : d152486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148374, d152486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148374, d152486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148375 q = 1) (hb : d152487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148375, d152487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148375, d152487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d148376 q = 1) (hb : d152488 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148376, d152488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148376, d152488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148380 q = 1) (hb : d152492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148380, d152492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148380, d152492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29893 q ha hb
  have h12 (q : Pattern) (ha : d148382 q = 1) (hb : d152494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148382, d152494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148382, d152494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29894 q ha hb
  have h13 (q : Pattern) (ha : d148383 q = 1) (hb : d152495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148383, d152495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148383, d152495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148384 q = 1) (hb : d152496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148384, d152496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148384, d152496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148385 q = 1) (hb : d152497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148385, d152497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d148385, d152497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d148386 q = 1) (hb : d152498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148386, d152498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148386, d152498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148480 q = 1) (hb : d152555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148480, d152555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148480, d152555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29906 q ha hb
  have h18 (q : Pattern) (ha : d148487 q = 1) (hb : d152566 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148487, d152566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148487, d152566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29908 q ha hb
  have h19 (q : Pattern) (ha : d148488 q = 1) (hb : d152567 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148488, d152567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148488, d152567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148489 q = 1) (hb : d152568 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148489, d152568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148489, d152568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d148490 q = 1) (hb : d152569 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148490, d152569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d148490, d152569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d148491 q = 1) (hb : d152570 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148491, d152570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148491, d152570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148492 q = 1) (hb : d152571 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148492, d152571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148492, d152571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29910 (p : Pattern) (ha : d148498 p = 1) (hb : d152577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148493 q = 1) (hb : d152572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148493, d152572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148493, d152572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29909 q ha hb
  have h2 (q : Pattern) (ha : d148494 q = 1) (hb : d152573 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148494, d152573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148494, d152573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148495 q = 1) (hb : d152574 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148495, d152574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148495, d152574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148496 q = 1) (hb : d152575 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148496, d152575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148496, d152575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148497 q = 1) (hb : d152576 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148497, d152576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148497, d152576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148498 q = 1) (hb : d152577 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148498, d152577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148498, d152577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29911 (p : Pattern) (ha : d148504 p = 1) (hb : d152583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d147261 q = 1) (hb : d151664 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147261, d151664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29668 q ha hb
    | true =>
      simp only [d147261, d151664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29708 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147500 q = 1) (hb : d151866 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147500, d151866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147500, d151866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29749 q ha hb
  have h3 (q : Pattern) (ha : d147501 q = 1) (hb : d151867 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147501, d151867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147501, d151867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147858 q = 1) (hb : d152103 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147858, d152103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147858, d152103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29803 q ha hb
  have h5 (q : Pattern) (ha : d147859 q = 1) (hb : d152104 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147859, d152104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147859, d152104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147860 q = 1) (hb : d152105 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d147860, d152105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147860, d152105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148199 q = 1) (hb : d152341 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148199, d152341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148199, d152341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29857 q ha hb
  have h8 (q : Pattern) (ha : d148200 q = 1) (hb : d152342 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148200, d152342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148200, d152342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148201 q = 1) (hb : d152343 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148201, d152343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148201, d152343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148202 q = 1) (hb : d152344 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148202, d152344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148202, d152344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148499 q = 1) (hb : d152578 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148499, d152578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148499, d152578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29910 q ha hb
  have h12 (q : Pattern) (ha : d148500 q = 1) (hb : d152579 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148500, d152579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148500, d152579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148501 q = 1) (hb : d152580 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148501, d152580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148501, d152580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148502 q = 1) (hb : d152581 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148502, d152581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148502, d152581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148503 q = 1) (hb : d152582 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d148503, d152582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148503, d152582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148504 q = 1) (hb : d152583 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d148504, d152583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148504, d152583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro29912 (p : Pattern) (ha : d148510 p = 1) (hb : d152589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148505 q = 1) (hb : d152584 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d148505, d152584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29911 q ha hb
    | true =>
      simp only [d148505, d152584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148506 q = 1) (hb : d152585 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d148506, d152585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148506, d152585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148507 q = 1) (hb : d152586 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d148507, d152586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148507, d152586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148508 q = 1) (hb : d152587 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d148508, d152587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148508, d152587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148509 q = 1) (hb : d152588 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d148509, d152588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148509, d152588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148510 q = 1) (hb : d152589 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d148510, d152589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148510, d152589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29913 (p : Pattern) (ha : d148516 p = 1) (hb : d152595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148511 q = 1) (hb : d152590 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d148511, d152590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29912 q ha hb
    | true =>
      simp only [d148511, d152590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148512 q = 1) (hb : d152591 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d148512, d152591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148512, d152591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148513 q = 1) (hb : d152592 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d148513, d152592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148513, d152592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148514 q = 1) (hb : d152593 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d148514, d152593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148514, d152593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148515 q = 1) (hb : d152594 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d148515, d152594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148515, d152594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148516 q = 1) (hb : d152595 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d148516, d152595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148516, d152595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29914 (p : Pattern) (ha : d148522 p = 1) (hb : d152601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148517 q = 1) (hb : d152596 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d148517, d152596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29913 q ha hb
    | true =>
      simp only [d148517, d152596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148518 q = 1) (hb : d152597 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d148518, d152597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148518, d152597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148519 q = 1) (hb : d152598 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d148519, d152598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148519, d152598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148520 q = 1) (hb : d152599 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d148520, d152599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148520, d152599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148521 q = 1) (hb : d152600 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d148521, d152600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148521, d152600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148522 q = 1) (hb : d152601 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d148522, d152601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148522, d152601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29915 (p : Pattern) (ha : d148528 p = 1) (hb : d152607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148523 q = 1) (hb : d152602 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d148523, d152602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29914 q ha hb
    | true =>
      simp only [d148523, d152602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148524 q = 1) (hb : d152603 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d148524, d152603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148524, d152603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148525 q = 1) (hb : d152604 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d148525, d152604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148525, d152604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148526 q = 1) (hb : d152605 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d148526, d152605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148526, d152605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148527 q = 1) (hb : d152606 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d148527, d152606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148527, d152606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148528 q = 1) (hb : d152607 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d148528, d152607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148528, d152607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29916 (p : Pattern) (ha : d148534 p = 1) (hb : d152613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148529 q = 1) (hb : d152608 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d148529, d152608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29915 q ha hb
    | true =>
      simp only [d148529, d152608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148530 q = 1) (hb : d152609 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d148530, d152609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148530, d152609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148531 q = 1) (hb : d152610 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d148531, d152610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148531, d152610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148532 q = 1) (hb : d152611 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d148532, d152611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148532, d152611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148533 q = 1) (hb : d152612 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d148533, d152612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148533, d152612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148534 q = 1) (hb : d152613 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d148534, d152613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148534, d152613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29917 (p : Pattern) (ha : d148540 p = 1) (hb : d152619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148535 q = 1) (hb : d152614 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d148535, d152614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29916 q ha hb
    | true =>
      simp only [d148535, d152614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148536 q = 1) (hb : d152615 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d148536, d152615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148536, d152615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148537 q = 1) (hb : d152616 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d148537, d152616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148537, d152616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148538 q = 1) (hb : d152617 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d148538, d152617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148538, d152617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148539 q = 1) (hb : d152618 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d148539, d152618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148539, d152618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148540 q = 1) (hb : d152619 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d148540, d152619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148540, d152619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29918 (p : Pattern) (ha : d148546 p = 1) (hb : d152625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148541 q = 1) (hb : d152620 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d148541, d152620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29917 q ha hb
    | true =>
      simp only [d148541, d152620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148542 q = 1) (hb : d152621 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d148542, d152621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148542, d152621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148543 q = 1) (hb : d152622 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d148543, d152622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148543, d152622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148544 q = 1) (hb : d152623 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d148544, d152623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148544, d152623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148545 q = 1) (hb : d152624 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d148545, d152624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148545, d152624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148546 q = 1) (hb : d152625 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d148546, d152625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148546, d152625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29919 (p : Pattern) (ha : d146836 p = 1) (hb : d150329 p = 1) : d152628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d146836 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12241 q = 1) (hb : d146836 q = 1) : d151304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29346 q ha hb
    | true =>
      simp only [d12241, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12292 q = 1) (hb : d146836 q = 1) : d151358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12293 q = 1) (hb : d146836 q = 1) : d151359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12293, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12294 q = 1) (hb : d146836 q = 1) : d151360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12295 q = 1) (hb : d146836 q = 1) : d151361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150329 q = 1) : d152628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150329, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150329, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro29920 (p : Pattern) (ha : d146836 p = 1) (hb : d150339 p = 1) : d152638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d146836 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12268 q = 1) (hb : d146836 q = 1) : d151334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29351 q ha hb
    | true =>
      simp only [d12268, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150335 q = 1) : d152634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150335, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150335, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150336 q = 1) : d152635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150336, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150336, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150337 q = 1) : d152636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150337, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150337, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150338 q = 1) : d152637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150338, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150338, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150339 q = 1) : d152638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150339, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150339, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29921 (p : Pattern) (ha : d146836 p = 1) (hb : d150345 p = 1) : d152644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d146836 q = 1) : d151363 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29354 q ha hb
    | true =>
      simp only [d12297, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29355 q ha hb
  have h2 (q : Pattern) (ha : d12298 q = 1) (hb : d146836 q = 1) : d151364 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150327 q = 1) : d152626 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150327, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150327, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150328 q = 1) : d152627 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150328, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150328, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150330 q = 1) : d152629 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150330, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150330, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29919 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150331 q = 1) : d152630 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150331, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150331, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150332 q = 1) : d152631 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150332, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150332, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150333 q = 1) : d152632 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150333, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150333, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150334 q = 1) : d152633 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150334, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150334, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150340 q = 1) : d152639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150340, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150340, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29920 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150341 q = 1) : d152640 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150341, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150341, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150342 q = 1) : d152641 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150342, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150342, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150343 q = 1) : d152642 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150343, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150343, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150344 q = 1) : d152643 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150344, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150344, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150345 q = 1) : d152644 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150345, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150345, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29922 (p : Pattern) (ha : d146836 p = 1) (hb : d150351 p = 1) : d152650 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d146836 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150346 q = 1) : d152645 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150346, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150346, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29921 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150347 q = 1) : d152646 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150347, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150347, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150348 q = 1) : d152647 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150348, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150348, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150349 q = 1) : d152648 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150349, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150349, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150350 q = 1) : d152649 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150350, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150350, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150351 q = 1) : d152650 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150351, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150351, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29923 (p : Pattern) (ha : d146836 p = 1) (hb : d150354 p = 1) : d152653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12463 q = 1) (hb : d146836 q = 1) : d151498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29382 q ha hb
    | true =>
      simp only [d12463, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29383 q ha hb
  have h2 (q : Pattern) (ha : d12464 q = 1) (hb : d146836 q = 1) : d151499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12465 q = 1) (hb : d146836 q = 1) : d151500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12465, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12466 q = 1) (hb : d146836 q = 1) : d151501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12467 q = 1) (hb : d146836 q = 1) : d151502 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150354 q = 1) : d152653 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150354, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150354, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29924 (p : Pattern) (ha : d146836 p = 1) (hb : d150365 p = 1) : d152664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150360 q = 1) : d152659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150360, d152659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29415 q hb ha
    | true =>
      simp only [d150360, d152659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29389 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150361 q = 1) : d152660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150361, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150361, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150362 q = 1) : d152661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150362, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150362, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150363 q = 1) : d152662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150363, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150363, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150364 q = 1) : d152663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150364, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150364, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150365 q = 1) : d152664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150365, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150365, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29925 (p : Pattern) (ha : d146836 p = 1) (hb : d150371 p = 1) : d152670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12469 q = 1) (hb : d146836 q = 1) : d151504 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29381 q ha hb
    | true =>
      simp only [d12469, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29384 q ha hb
  have h2 (q : Pattern) (ha : d12470 q = 1) (hb : d146836 q = 1) : d151505 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12470, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150352 q = 1) : d152651 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150352, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150352, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150353 q = 1) : d152652 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150353, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150353, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150355 q = 1) : d152654 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150355, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150355, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29923 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150356 q = 1) : d152655 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150356, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150356, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150357 q = 1) : d152656 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150357, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150357, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150358 q = 1) : d152657 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150358, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150358, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150359 q = 1) : d152658 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150359, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150359, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150366 q = 1) : d152665 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150366, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150366, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29924 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150367 q = 1) : d152666 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150367, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150367, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150368 q = 1) : d152667 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150368, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150368, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150369 q = 1) : d152668 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150369, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150369, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150370 q = 1) : d152669 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150370, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150370, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150371 q = 1) : d152670 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150371, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150371, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29926 (p : Pattern) (ha : d146836 p = 1) (hb : d150377 p = 1) : d152676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150372 q = 1) : d152671 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150372, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150372, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29925 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150373 q = 1) : d152672 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150373, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150373, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150374 q = 1) : d152673 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150374, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150374, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150375 q = 1) : d152674 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150375, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150375, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150376 q = 1) : d152675 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150376, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150376, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150377 q = 1) : d152676 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150377, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150377, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29927 (p : Pattern) (ha : d146836 p = 1) (hb : d150381 p = 1) : d152680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12718 q = 1) (hb : d146836 q = 1) : d151696 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29426 q ha hb
    | true =>
      simp only [d12718, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29427 q ha hb
  have h2 (q : Pattern) (ha : d12719 q = 1) (hb : d146836 q = 1) : d151697 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12720 q = 1) (hb : d146836 q = 1) : d151698 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12720, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12721 q = 1) (hb : d146836 q = 1) : d151699 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12722 q = 1) (hb : d146836 q = 1) : d151700 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150381 q = 1) : d152680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150381, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150381, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29928 (p : Pattern) (ha : d146836 p = 1) (hb : d150392 p = 1) : d152691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150387 q = 1) : d152686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150387, d152686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29460 q hb ha
    | true =>
      simp only [d150387, d152686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29434 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150388 q = 1) : d152687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150388, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150388, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150389 q = 1) : d152688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150389, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150389, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150390 q = 1) : d152689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150390, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150390, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150391 q = 1) : d152690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150391, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150391, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150392 q = 1) : d152691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150392, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150392, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29929 (p : Pattern) (ha : d146836 p = 1) (hb : d150398 p = 1) : d152697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12724 q = 1) (hb : d146836 q = 1) : d151702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29425 q ha hb
    | true =>
      simp only [d12724, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29428 q ha hb
  have h2 (q : Pattern) (ha : d12725 q = 1) (hb : d146836 q = 1) : d151703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12725, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150379 q = 1) : d152678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150379, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150379, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150380 q = 1) : d152679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150380, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150380, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150382 q = 1) : d152681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150382, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150382, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29927 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150383 q = 1) : d152682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150383, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150383, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150384 q = 1) : d152683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150384, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150384, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150385 q = 1) : d152684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150385, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150385, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150386 q = 1) : d152685 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150386, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150386, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150393 q = 1) : d152692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150393, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150393, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29928 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150394 q = 1) : d152693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150394, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150394, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150395 q = 1) : d152694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150395, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150395, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150396 q = 1) : d152695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150396, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150396, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150397 q = 1) : d152696 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150397, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150397, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150398 q = 1) : d152697 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150398, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150398, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29930 (p : Pattern) (ha : d146836 p = 1) (hb : d150404 p = 1) : d152703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150399 q = 1) : d152698 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150399, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150399, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29929 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150400 q = 1) : d152699 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150400, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150400, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150401 q = 1) : d152700 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150401, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150401, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150402 q = 1) : d152701 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150402, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150402, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150403 q = 1) : d152702 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150403, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150403, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150404 q = 1) : d152703 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150404, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150404, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29931 (p : Pattern) (ha : d146836 p = 1) (hb : d150409 p = 1) : d152708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12992 q = 1) (hb : d146836 q = 1) : d151906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29475 q ha hb
    | true =>
      simp only [d12992, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29476 q ha hb
  have h2 (q : Pattern) (ha : d12993 q = 1) (hb : d146836 q = 1) : d151907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12994 q = 1) (hb : d146836 q = 1) : d151908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12994, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12995 q = 1) (hb : d146836 q = 1) : d151909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12996 q = 1) (hb : d146836 q = 1) : d151910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150409 q = 1) : d152708 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150409, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150409, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29932 (p : Pattern) (ha : d146836 p = 1) (hb : d150418 p = 1) : d152717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d146836 q = 1) : d152068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29516 q ha hb
    | true =>
      simp only [d13244, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d146836 q = 1) : d152069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d146836 q = 1) : d152058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29485 q ha hb
    | true =>
      simp only [d13197, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d146836 q = 1) : d152059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150415 q = 1) : d152714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150415, d152714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150415, d152714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150416 q = 1) : d152715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150416, d152715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150416, d152715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150417 q = 1) : d152716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150417, d152716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150417, d152716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150418 q = 1) : d152717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150418, d152717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150418, d152717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29933 (p : Pattern) (ha : d146836 p = 1) (hb : d150424 p = 1) : d152723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150419 q = 1) : d152718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150419, d152718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29932 q ha hb
    | true =>
      simp only [d150419, d152718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29486 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150420 q = 1) : d152719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150420, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150420, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150421 q = 1) : d152720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150421, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150421, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150422 q = 1) : d152721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150422, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150422, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150423 q = 1) : d152722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150423, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150423, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150424 q = 1) : d152723 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150424, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150424, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29934 (p : Pattern) (ha : d146836 p = 1) (hb : d150430 p = 1) : d152729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12998 q = 1) (hb : d146836 q = 1) : d151912 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29474 q ha hb
    | true =>
      simp only [d12998, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29477 q ha hb
  have h2 (q : Pattern) (ha : d12999 q = 1) (hb : d146836 q = 1) : d151913 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12999, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150407 q = 1) : d152706 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150407, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150407, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150408 q = 1) : d152707 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150408, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150408, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150410 q = 1) : d152709 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150410, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150410, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29931 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150411 q = 1) : d152710 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150411, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150411, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150412 q = 1) : d152711 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150412, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150412, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150413 q = 1) : d152712 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150413, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150413, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150414 q = 1) : d152713 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150414, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150414, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150425 q = 1) : d152724 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150425, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150425, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29933 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150426 q = 1) : d152725 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150426, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150426, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150427 q = 1) : d152726 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150427, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150427, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150428 q = 1) : d152727 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150428, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150428, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150429 q = 1) : d152728 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150429, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150429, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150430 q = 1) : d152729 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150430, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150430, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29935 (p : Pattern) (ha : d146836 p = 1) (hb : d150436 p = 1) : d152735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150431 q = 1) : d152730 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150431, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150431, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29934 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150432 q = 1) : d152731 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150432, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150432, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150433 q = 1) : d152732 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150433, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150433, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150434 q = 1) : d152733 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150434, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150434, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150435 q = 1) : d152734 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150435, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150435, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150436 q = 1) : d152735 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150436, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150436, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29936 (p : Pattern) (ha : d146836 p = 1) (hb : d150442 p = 1) : d152741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13318 q = 1) (hb : d146836 q = 1) : d152144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29531 q ha hb
    | true =>
      simp only [d13318, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29532 q ha hb
  have h2 (q : Pattern) (ha : d13319 q = 1) (hb : d146836 q = 1) : d152145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13320 q = 1) (hb : d146836 q = 1) : d152146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13320, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13321 q = 1) (hb : d146836 q = 1) : d152147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13322 q = 1) (hb : d146836 q = 1) : d152148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150442 q = 1) : d152741 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150442, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150442, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29937 (p : Pattern) (ha : d146836 p = 1) (hb : d150451 p = 1) : d152750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d146836 q = 1) : d152306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29572 q ha hb
    | true =>
      simp only [d13570, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d146836 q = 1) : d152307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d146836 q = 1) : d152296 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29541 q ha hb
    | true =>
      simp only [d13523, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d146836 q = 1) : d152297 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150448 q = 1) : d152747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150448, d152747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150448, d152747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150449 q = 1) : d152748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150449, d152748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150449, d152748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150450 q = 1) : d152749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150450, d152749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150450, d152749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150451 q = 1) : d152750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150451, d152750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150451, d152750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29938 (p : Pattern) (ha : d146836 p = 1) (hb : d150457 p = 1) : d152756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150452 q = 1) : d152751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150452, d152751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29937 q ha hb
    | true =>
      simp only [d150452, d152751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29542 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150453 q = 1) : d152752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150453, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150453, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150454 q = 1) : d152753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150454, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150454, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150455 q = 1) : d152754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150455, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150455, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150456 q = 1) : d152755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150456, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150456, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150457 q = 1) : d152756 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150457, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150457, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29939 (p : Pattern) (ha : d146836 p = 1) (hb : d150463 p = 1) : d152762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13324 q = 1) (hb : d146836 q = 1) : d152150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29530 q ha hb
    | true =>
      simp only [d13324, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29533 q ha hb
  have h2 (q : Pattern) (ha : d13325 q = 1) (hb : d146836 q = 1) : d152151 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13325, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150440 q = 1) : d152739 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150440, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150440, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150441 q = 1) : d152740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150441, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150441, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150443 q = 1) : d152742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150443, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150443, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29936 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150444 q = 1) : d152743 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150444, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150444, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150445 q = 1) : d152744 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150445, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150445, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150446 q = 1) : d152745 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150446, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150446, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150447 q = 1) : d152746 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150447, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150447, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150458 q = 1) : d152757 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150458, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150458, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29938 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150459 q = 1) : d152758 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150459, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150459, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150460 q = 1) : d152759 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150460, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150460, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150461 q = 1) : d152760 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150461, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150461, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150462 q = 1) : d152761 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150462, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150462, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150463 q = 1) : d152762 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150463, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150463, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29940 (p : Pattern) (ha : d146836 p = 1) (hb : d150469 p = 1) : d152768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150464 q = 1) : d152763 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150464, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150464, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29939 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150465 q = 1) : d152764 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150465, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150465, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150466 q = 1) : d152765 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150466, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150466, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150467 q = 1) : d152766 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150467, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150467, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150468 q = 1) : d152767 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150468, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150468, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150469 q = 1) : d152768 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150469, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150469, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29941 (p : Pattern) (ha : d146836 p = 1) (hb : d150476 p = 1) : d152775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13645 q = 1) (hb : d146836 q = 1) : d152383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29587 q ha hb
    | true =>
      simp only [d13645, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29588 q ha hb
  have h2 (q : Pattern) (ha : d13646 q = 1) (hb : d146836 q = 1) : d152384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13647 q = 1) (hb : d146836 q = 1) : d152385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13647, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13648 q = 1) (hb : d146836 q = 1) : d152386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13649 q = 1) (hb : d146836 q = 1) : d152387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150476 q = 1) : d152775 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150476, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150476, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29942 (p : Pattern) (ha : d146836 p = 1) (hb : d150485 p = 1) : d152784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d146836 q = 1) : d152543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29625 q ha hb
    | true =>
      simp only [d13897, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d146836 q = 1) : d152544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d146836 q = 1) : d152533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29597 q ha hb
    | true =>
      simp only [d13850, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d146836 q = 1) : d152534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150482 q = 1) : d152781 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150482, d152781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150482, d152781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150483 q = 1) : d152782 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150483, d152782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150483, d152782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150484 q = 1) : d152783 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150484, d152783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150484, d152783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150485 q = 1) : d152784 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150485, d152784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150485, d152784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29943 (p : Pattern) (ha : d146836 p = 1) (hb : d150491 p = 1) : d152790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150486 q = 1) : d152785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150486, d152785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29942 q ha hb
    | true =>
      simp only [d150486, d152785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29598 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150487 q = 1) : d152786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150487, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150487, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150488 q = 1) : d152787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150488, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150488, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150489 q = 1) : d152788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150489, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150489, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150490 q = 1) : d152789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150490, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150490, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150491 q = 1) : d152790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150491, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150491, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29944 (p : Pattern) (ha : d146836 p = 1) (hb : d150497 p = 1) : d152796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13651 q = 1) (hb : d146836 q = 1) : d152389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29586 q ha hb
    | true =>
      simp only [d13651, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29589 q ha hb
  have h2 (q : Pattern) (ha : d13652 q = 1) (hb : d146836 q = 1) : d152390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13652, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150474 q = 1) : d152773 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150474, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150474, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150475 q = 1) : d152774 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150475, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150475, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150477 q = 1) : d152776 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150477, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150477, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29941 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150478 q = 1) : d152777 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150478, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150478, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150479 q = 1) : d152778 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150479, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150479, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150480 q = 1) : d152779 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150480, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150480, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150481 q = 1) : d152780 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150481, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150481, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150492 q = 1) : d152791 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150492, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150492, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29943 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150493 q = 1) : d152792 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150493, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150493, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150494 q = 1) : d152793 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150494, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150494, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150495 q = 1) : d152794 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150495, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150495, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150496 q = 1) : d152795 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150496, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150496, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150497 q = 1) : d152796 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150497, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150497, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29945 (p : Pattern) (ha : d146836 p = 1) (hb : d150503 p = 1) : d152802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150498 q = 1) : d152797 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150498, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150498, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29944 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150499 q = 1) : d152798 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150499, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150499, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150500 q = 1) : d152799 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150500, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150500, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150501 q = 1) : d152800 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150501, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150501, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150502 q = 1) : d152801 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150502, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150502, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150503 q = 1) : d152802 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150503, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150503, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29946 (p : Pattern) (ha : d146836 p = 1) (hb : d150509 p = 1) : d152808 p = 1 := by
  have h0 (q : Pattern) (ha : d146836 q = 1) (hb : d150378 q = 1) : d152677 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150378, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29922 q ha hb
    | true =>
      simp only [d150378, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29926 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150405 q = 1) : d152704 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150405, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150405, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29930 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150406 q = 1) : d152705 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150406, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150406, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150437 q = 1) : d152736 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150437, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150437, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29935 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150438 q = 1) : d152737 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150438, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150438, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150439 q = 1) : d152738 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150439, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150439, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150470 q = 1) : d152769 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150470, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150470, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29940 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150471 q = 1) : d152770 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150471, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150471, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150472 q = 1) : d152771 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150472, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150472, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150473 q = 1) : d152772 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150473, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150473, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150504 q = 1) : d152803 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150504, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150504, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29945 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150505 q = 1) : d152804 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150505, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150505, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150506 q = 1) : d152805 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150506, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150506, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150507 q = 1) : d152806 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150507, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150507, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150508 q = 1) : d152807 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150508, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150508, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d150509 q = 1) : d152808 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150509, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150509, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro29947 (p : Pattern) (ha : d146836 p = 1) (hb : d150515 p = 1) : d152814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150510 q = 1) : d152809 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150510, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29946 q ha hb
    | true =>
      simp only [d150510, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150511 q = 1) : d152810 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150511, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150511, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150512 q = 1) : d152811 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150512, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150512, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150513 q = 1) : d152812 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150513, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150513, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150514 q = 1) : d152813 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150514, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150514, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150515 q = 1) : d152814 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150515, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150515, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29948 (p : Pattern) (ha : d146836 p = 1) (hb : d150521 p = 1) : d152820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150516 q = 1) : d152815 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150516, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29947 q ha hb
    | true =>
      simp only [d150516, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150517 q = 1) : d152816 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150517, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150517, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150518 q = 1) : d152817 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150518, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150518, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150519 q = 1) : d152818 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150519, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150519, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150520 q = 1) : d152819 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150520, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150520, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150521 q = 1) : d152820 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150521, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150521, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29949 (p : Pattern) (ha : d146836 p = 1) (hb : d150527 p = 1) : d152826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150522 q = 1) : d152821 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150522, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29948 q ha hb
    | true =>
      simp only [d150522, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150523 q = 1) : d152822 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150523, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150523, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150524 q = 1) : d152823 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150524, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150524, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150525 q = 1) : d152824 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150525, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150525, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150526 q = 1) : d152825 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150526, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150526, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150527 q = 1) : d152826 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150527, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150527, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29950 (p : Pattern) (ha : d146836 p = 1) (hb : d150533 p = 1) : d152832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150528 q = 1) : d152827 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150528, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29949 q ha hb
    | true =>
      simp only [d150528, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150529 q = 1) : d152828 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150529, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150529, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150530 q = 1) : d152829 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150530, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150530, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150531 q = 1) : d152830 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150531, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150531, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150532 q = 1) : d152831 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150532, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150532, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150533 q = 1) : d152832 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150533, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150533, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29951 (p : Pattern) (ha : d146836 p = 1) (hb : d150539 p = 1) : d152838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150534 q = 1) : d152833 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150534, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29950 q ha hb
    | true =>
      simp only [d150534, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150535 q = 1) : d152834 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150535, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150535, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150536 q = 1) : d152835 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150536, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150536, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150537 q = 1) : d152836 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150537, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150537, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150538 q = 1) : d152837 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150538, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150538, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150539 q = 1) : d152838 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150539, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150539, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29952 (p : Pattern) (ha : d146836 p = 1) (hb : d150545 p = 1) : d152844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150540 q = 1) : d152839 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150540, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29951 q ha hb
    | true =>
      simp only [d150540, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150541 q = 1) : d152840 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150541, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150541, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150542 q = 1) : d152841 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150542, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150542, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150543 q = 1) : d152842 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150543, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150543, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150544 q = 1) : d152843 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150544, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150544, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150545 q = 1) : d152844 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150545, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150545, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29953 (p : Pattern) (ha : d146836 p = 1) (hb : d150551 p = 1) : d152850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150546 q = 1) : d152845 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150546, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29952 q ha hb
    | true =>
      simp only [d150546, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150547 q = 1) : d152846 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150547, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150547, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150548 q = 1) : d152847 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150548, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150548, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150549 q = 1) : d152848 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150549, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150549, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150550 q = 1) : d152849 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150550, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150550, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150551 q = 1) : d152850 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150551, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150551, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29954 (p : Pattern) (ha : d146966 p = 1) (hb : d151355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146928 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d146955 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d146852 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29639 q ha hb
    | true =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d146956 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d146956, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d146962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d146963 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146963, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d146964 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d146964, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146965 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146965, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146966 q = 1) (hb : d151355 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146966, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146966, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29955 (p : Pattern) (ha : d146985 p = 1) (hb : d151362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146928 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146955 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146852 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29639 q ha hb
    | true =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d146956 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d146956, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d146962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d146963 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146963, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d146964 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146964, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146965 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146965, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d146971 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d146975 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d146977 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d146859 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29641 q ha hb
    | true =>
      simp only [d146859, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d146978 q = 1) (hb : d151358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d146978, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d146981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146982 q = 1) (hb : d151359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146982, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d146983 q = 1) (hb : d151360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146983, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d146983, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146984 q = 1) (hb : d151361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146984, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d146984, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146985 q = 1) (hb : d151362 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146985, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146985, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29956 (p : Pattern) (ha : d146994 p = 1) (hb : d152628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146977 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146859 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29641 q ha hb
    | true =>
      simp only [d146859, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d146978 q = 1) (hb : d151358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146978, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146982 q = 1) (hb : d151359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146982, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146992 q = 1) (hb : d151360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146992, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146992, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146993 q = 1) (hb : d151361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146993, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146993, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146994 q = 1) (hb : d152628 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146994, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146994, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29957 (p : Pattern) (ha : d147030 p = 1) (hb : d152638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147019 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146891 q = 1) (hb : d151334 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146891, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29645 q ha hb
    | true =>
      simp only [d146891, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d147020 q = 1) (hb : d152634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147020, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147020, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147027 q = 1) (hb : d152635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147027, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147027, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147028 q = 1) (hb : d152636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147028, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147028, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147029 q = 1) (hb : d152637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147029, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147029, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147030 q = 1) (hb : d152638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147030, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147030, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29958 (p : Pattern) (ha : d147036 p = 1) (hb : d152644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146922 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146986 q = 1) (hb : d151363 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146986, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29954 q ha hb
    | true =>
      simp only [d146986, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29955 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146989 q = 1) (hb : d151364 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146989, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146989, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146990 q = 1) (hb : d152626 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146990, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146990, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146991 q = 1) (hb : d152627 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146991, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146991, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146995 q = 1) (hb : d152629 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146995, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146995, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29956 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d146996 q = 1) (hb : d152630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146996, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146996, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146997 q = 1) (hb : d152631 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146997, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146997, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d146998 q = 1) (hb : d152632 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146998, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146998, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d146999 q = 1) (hb : d152633 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146999, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146999, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147031 q = 1) (hb : d152639 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147031, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147031, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29957 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147032 q = 1) (hb : d152640 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147032, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147032, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147033 q = 1) (hb : d152641 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147033, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147033, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147034 q = 1) (hb : d152642 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147034, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147034, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147035 q = 1) (hb : d152643 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147035, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147035, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147036 q = 1) (hb : d152644 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147036, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147036, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29959 (p : Pattern) (ha : d147042 p = 1) (hb : d152650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d146903 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d146903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d146903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28391 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d146904 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d146904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d146904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d146905 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d146905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d146905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d146906 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d146906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d146906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d146907 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d146907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d146907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147037 q = 1) (hb : d152645 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147037, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147037, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29958 q ha hb
  have h8 (q : Pattern) (ha : d147038 q = 1) (hb : d152646 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147038, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147038, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147039 q = 1) (hb : d152647 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147039, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147039, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147040 q = 1) (hb : d152648 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147040, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147040, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147041 q = 1) (hb : d152649 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147041, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147041, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d147042 q = 1) (hb : d152650 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147042, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147042, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro29960 (p : Pattern) (ha : d147136 p = 1) (hb : d151493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147060 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29671 q ha hb
    | true =>
      simp only [d147060, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29672 q ha hb
  have h5 (q : Pattern) (ha : d147126 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147126, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147132 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147133 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147133, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147134 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147134, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147135 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147135, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147136 q = 1) (hb : d151493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147136, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147136, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29961 (p : Pattern) (ha : d147157 p = 1) (hb : d151503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147060 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29671 q ha hb
    | true =>
      simp only [d147060, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29672 q ha hb
  have h4 (q : Pattern) (ha : d147126 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147126, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147132 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147133 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147133, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147134 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147134, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147135 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147135, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147142 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147147 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147149 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147070 q = 1) (hb : d151498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29674 q ha hb
    | true =>
      simp only [d147070, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29675 q ha hb
  have h13 (q : Pattern) (ha : d147150 q = 1) (hb : d151499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147150, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147154 q = 1) (hb : d151500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147154, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147155 q = 1) (hb : d151501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147155, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147155, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147156 q = 1) (hb : d151502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147156, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147156, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147157 q = 1) (hb : d151503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147157, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147157, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29962 (p : Pattern) (ha : d147177 p = 1) (hb : d152653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147149 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147070 q = 1) (hb : d151498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29674 q ha hb
    | true =>
      simp only [d147070, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29675 q ha hb
  have h3 (q : Pattern) (ha : d147150 q = 1) (hb : d151499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147150, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147154 q = 1) (hb : d151500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147154, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147175 q = 1) (hb : d151501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147175, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147175, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147176 q = 1) (hb : d151502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147176, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147176, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147177 q = 1) (hb : d152653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147177, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147177, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29963 (p : Pattern) (ha : d147241 p = 1) (hb : d152664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147230 q = 1) (hb : d152659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147230, d152659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29702 q ha hb
    | true =>
      simp only [d147230, d152659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29705 q ha hb
  have h3 (q : Pattern) (ha : d147231 q = 1) (hb : d152660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147231, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147231, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147237 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147238 q = 1) (hb : d152661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147238, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147238, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147239 q = 1) (hb : d152662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147239, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147239, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147240 q = 1) (hb : d152663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147240, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147240, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147241 q = 1) (hb : d152664 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147241, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147241, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29964 (p : Pattern) (ha : d147254 p = 1) (hb : d152670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147078 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147158 q = 1) (hb : d151504 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147158, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29960 q ha hb
    | true =>
      simp only [d147158, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29961 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147172 q = 1) (hb : d151505 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147172, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147172, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147173 q = 1) (hb : d152651 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147173, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147173, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147174 q = 1) (hb : d152652 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147174, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147174, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147178 q = 1) (hb : d152654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147178, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147178, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29962 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147180 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147181 q = 1) (hb : d152655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147181, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147181, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147182 q = 1) (hb : d152656 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147182, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147182, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147183 q = 1) (hb : d152657 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147183, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147183, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147184 q = 1) (hb : d152658 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147184, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147184, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147242 q = 1) (hb : d152665 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147242, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147242, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29963 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147249 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147250 q = 1) (hb : d152666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147250, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147250, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147251 q = 1) (hb : d152667 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147251, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147251, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147252 q = 1) (hb : d152668 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147252, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147252, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147253 q = 1) (hb : d152669 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147253, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147253, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147254 q = 1) (hb : d152670 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147254, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147254, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29965 (p : Pattern) (ha : d147260 p = 1) (hb : d152676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147255 q = 1) (hb : d152671 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147255, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147255, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29964 q ha hb
  have h2 (q : Pattern) (ha : d147256 q = 1) (hb : d152672 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147256, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147256, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147257 q = 1) (hb : d152673 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147257, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147257, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147258 q = 1) (hb : d152674 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147258, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147258, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147259 q = 1) (hb : d152675 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147259, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147259, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147260 q = 1) (hb : d152676 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147260, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147260, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29966 (p : Pattern) (ha : d147365 p = 1) (hb : d151691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147354 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147289 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29711 q ha hb
    | true =>
      simp only [d147289, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29712 q ha hb
  have h5 (q : Pattern) (ha : d147355 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147355, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147361 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147362 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147362, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147363 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147363, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147364 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147364, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147365 q = 1) (hb : d151691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147365, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147365, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29967 (p : Pattern) (ha : d147386 p = 1) (hb : d151701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147354 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147289 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29711 q ha hb
    | true =>
      simp only [d147289, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29712 q ha hb
  have h4 (q : Pattern) (ha : d147355 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147355, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147361 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147362 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147362, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147363 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147363, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147364 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147364, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147376 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147378 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147299 q = 1) (hb : d151696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29714 q ha hb
    | true =>
      simp only [d147299, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29715 q ha hb
  have h13 (q : Pattern) (ha : d147379 q = 1) (hb : d151697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147379, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147382 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147383 q = 1) (hb : d151698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147383, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147384 q = 1) (hb : d151699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147384, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147384, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147385 q = 1) (hb : d151700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147385, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147385, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147386 q = 1) (hb : d151701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147386, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147386, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29968 (p : Pattern) (ha : d147406 p = 1) (hb : d152680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147378 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147299 q = 1) (hb : d151696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29714 q ha hb
    | true =>
      simp only [d147299, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29715 q ha hb
  have h3 (q : Pattern) (ha : d147379 q = 1) (hb : d151697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147379, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147382 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147383 q = 1) (hb : d151698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147383, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147404 q = 1) (hb : d151699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147404, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147404, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147405 q = 1) (hb : d151700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147405, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147405, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147406 q = 1) (hb : d152680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147406, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147406, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29969 (p : Pattern) (ha : d147480 p = 1) (hb : d152691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147464 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147469 q = 1) (hb : d152686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147469, d152686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29743 q ha hb
    | true =>
      simp only [d147469, d152686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29746 q ha hb
  have h3 (q : Pattern) (ha : d147470 q = 1) (hb : d152687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147470, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147470, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147476 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147477 q = 1) (hb : d152688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147477, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147477, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147478 q = 1) (hb : d152689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147478, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147478, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147479 q = 1) (hb : d152690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147479, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147479, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147480 q = 1) (hb : d152691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147480, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147480, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29970 (p : Pattern) (ha : d147493 p = 1) (hb : d152697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147387 q = 1) (hb : d151702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147387, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29966 q ha hb
    | true =>
      simp only [d147387, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29967 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147401 q = 1) (hb : d151703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147401, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147401, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147402 q = 1) (hb : d152678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147402, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147402, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147403 q = 1) (hb : d152679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147403, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147403, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147407 q = 1) (hb : d152681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147407, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147407, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29968 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147409 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147410 q = 1) (hb : d152682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147410, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147410, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147411 q = 1) (hb : d152683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147411, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147411, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147412 q = 1) (hb : d152684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147412, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147412, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147413 q = 1) (hb : d152685 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147413, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147413, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147481 q = 1) (hb : d152692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147481, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147481, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29969 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147488 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147489 q = 1) (hb : d152693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147489, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147489, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147490 q = 1) (hb : d152694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147490, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147490, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147491 q = 1) (hb : d152695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147491, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147491, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147492 q = 1) (hb : d152696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147492, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147492, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147493 q = 1) (hb : d152697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147493, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147493, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29971 (p : Pattern) (ha : d147499 p = 1) (hb : d152703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147494 q = 1) (hb : d152698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147494, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147494, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29970 q ha hb
  have h2 (q : Pattern) (ha : d147495 q = 1) (hb : d152699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147495, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147495, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147496 q = 1) (hb : d152700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147496, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147496, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147497 q = 1) (hb : d152701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147497, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147497, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147498 q = 1) (hb : d152702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147498, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147498, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147499 q = 1) (hb : d152703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147499, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147499, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29972 (p : Pattern) (ha : d147664 p = 1) (hb : d151901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147599 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147644 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147564 q = 1) (hb : d151896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29755 q ha hb
    | true =>
      simp only [d147564, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29756 q ha hb
  have h5 (q : Pattern) (ha : d147645 q = 1) (hb : d151897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147645, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147660 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147661 q = 1) (hb : d151898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147661, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147662 q = 1) (hb : d151899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147662, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147663 q = 1) (hb : d151900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147663, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147664 q = 1) (hb : d151901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147664, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147664, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29973 (p : Pattern) (ha : d147686 p = 1) (hb : d151911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147590 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147644 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147564 q = 1) (hb : d151896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29755 q ha hb
    | true =>
      simp only [d147564, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29756 q ha hb
  have h4 (q : Pattern) (ha : d147645 q = 1) (hb : d151897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147645, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147660 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147661 q = 1) (hb : d151898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147661, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147662 q = 1) (hb : d151899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147662, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147663 q = 1) (hb : d151900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147663, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147670 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147675 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147678 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147574 q = 1) (hb : d151906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29758 q ha hb
    | true =>
      simp only [d147574, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29759 q ha hb
  have h13 (q : Pattern) (ha : d147679 q = 1) (hb : d151907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147679, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147682 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147683 q = 1) (hb : d151908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147683, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147684 q = 1) (hb : d151909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147684, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147684, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147685 q = 1) (hb : d151910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147685, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147685, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147686 q = 1) (hb : d151911 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147686, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147686, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29974 (p : Pattern) (ha : d147711 p = 1) (hb : d152708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147574 q = 1) (hb : d151906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29758 q ha hb
    | true =>
      simp only [d147574, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29759 q ha hb
  have h3 (q : Pattern) (ha : d147679 q = 1) (hb : d151907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147679, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147683 q = 1) (hb : d151908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147683, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147709 q = 1) (hb : d151909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147709, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147709, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147710 q = 1) (hb : d151910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147710, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147710, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147711 q = 1) (hb : d152708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147711, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147711, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29975 (p : Pattern) (ha : d147807 p = 1) (hb : d152067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147765 q = 1) (hb : d152031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28231 q ha hb
    | true =>
      simp only [d147765, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
  have h2 (q : Pattern) (ha : d147766 q = 1) (hb : d152032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147767 q = 1) (hb : d152033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147774 q = 1) (hb : d152035 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
    | true =>
      simp only [d147774, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29789 q ha hb
  have h5 (q : Pattern) (ha : d147775 q = 1) (hb : d152036 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147776 q = 1) (hb : d152037 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147777 q = 1) (hb : d152038 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147777, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147793 q = 1) (hb : d152052 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147793, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28232 q ha hb
    | true =>
      simp only [d147793, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29793 q hb ha
  have h9 (q : Pattern) (ha : d147794 q = 1) (hb : d152053 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147794, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147794, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147795 q = 1) (hb : d152054 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147795, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147795, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147796 q = 1) (hb : d152055 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147796, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147796, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147806 q = 1) (hb : d152066 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147806, d152066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147806, d152066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147807 q = 1) (hb : d152067 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147807, d152067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147807, d152067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29976 (p : Pattern) (ha : d147813 p = 1) (hb : d152717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147808 q = 1) (hb : d152068 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147808, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29975 q ha hb
    | true =>
      simp only [d147808, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147809 q = 1) (hb : d152069 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147809, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147809, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147799 q = 1) (hb : d152058 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147799, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29794 q ha hb
    | true =>
      simp only [d147799, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147800 q = 1) (hb : d152059 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147800, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147800, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147810 q = 1) (hb : d152714 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147810, d152714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147810, d152714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147811 q = 1) (hb : d152715 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147811, d152715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147811, d152715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147812 q = 1) (hb : d152716 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147812, d152716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147812, d152716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147813 q = 1) (hb : d152717 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147813, d152717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147813, d152717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29977 (p : Pattern) (ha : d147838 p = 1) (hb : d152723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147818 q = 1) (hb : d152718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147818, d152718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29976 q ha hb
    | true =>
      simp only [d147818, d152718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29800 q ha hb
  have h3 (q : Pattern) (ha : d147819 q = 1) (hb : d152719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147819, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147819, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147834 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147835 q = 1) (hb : d152720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147835, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147835, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147836 q = 1) (hb : d152721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147836, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147836, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147837 q = 1) (hb : d152722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147837, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147837, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147838 q = 1) (hb : d152723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147838, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147838, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29978 (p : Pattern) (ha : d147851 p = 1) (hb : d152729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147687 q = 1) (hb : d151912 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147687, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29972 q ha hb
    | true =>
      simp only [d147687, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29973 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147706 q = 1) (hb : d151913 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147706, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147706, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147707 q = 1) (hb : d152706 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147707, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147707, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147708 q = 1) (hb : d152707 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147708, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147708, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147712 q = 1) (hb : d152709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147712, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147712, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29974 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147714 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147715 q = 1) (hb : d152710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147715, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147715, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147716 q = 1) (hb : d152711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147716, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147716, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147717 q = 1) (hb : d152712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147717, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147717, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147718 q = 1) (hb : d152713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147718, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147718, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147839 q = 1) (hb : d152724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147839, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147839, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29977 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147846 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147847 q = 1) (hb : d152725 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147847, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147847, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147848 q = 1) (hb : d152726 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147848, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147848, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147849 q = 1) (hb : d152727 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147849, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147849, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147850 q = 1) (hb : d152728 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147850, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147850, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147851 q = 1) (hb : d152729 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147851, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147851, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29979 (p : Pattern) (ha : d147857 p = 1) (hb : d152735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147852 q = 1) (hb : d152730 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147852, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147852, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29978 q ha hb
  have h2 (q : Pattern) (ha : d147853 q = 1) (hb : d152731 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147853, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147853, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147854 q = 1) (hb : d152732 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147854, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147854, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147855 q = 1) (hb : d152733 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147855, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147855, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147856 q = 1) (hb : d152734 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147856, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147856, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147857 q = 1) (hb : d152735 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147857, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147857, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29980 (p : Pattern) (ha : d148013 p = 1) (hb : d152139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147953 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147993 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147918 q = 1) (hb : d152134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29809 q ha hb
    | true =>
      simp only [d147918, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29810 q ha hb
  have h5 (q : Pattern) (ha : d147994 q = 1) (hb : d152135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147994, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d148009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148010 q = 1) (hb : d152136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148010, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148011 q = 1) (hb : d152137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148011, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148012 q = 1) (hb : d152138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148012, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148013 q = 1) (hb : d152139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148013, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148013, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29981 (p : Pattern) (ha : d148035 p = 1) (hb : d152149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147944 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147953 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147918 q = 1) (hb : d152134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29809 q ha hb
    | true =>
      simp only [d147918, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29810 q ha hb
  have h4 (q : Pattern) (ha : d147994 q = 1) (hb : d152135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147994, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148010 q = 1) (hb : d152136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148010, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148011 q = 1) (hb : d152137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148011, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148012 q = 1) (hb : d152138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148012, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148019 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148024 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d148027 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147928 q = 1) (hb : d152144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29812 q ha hb
    | true =>
      simp only [d147928, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29813 q ha hb
  have h13 (q : Pattern) (ha : d148028 q = 1) (hb : d152145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d148028, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148031 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148032 q = 1) (hb : d152146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148032, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148033 q = 1) (hb : d152147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148033, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d148033, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148034 q = 1) (hb : d152148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148034, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148034, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148035 q = 1) (hb : d152149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148035, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148035, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29982 (p : Pattern) (ha : d148060 p = 1) (hb : d152741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147928 q = 1) (hb : d152144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29812 q ha hb
    | true =>
      simp only [d147928, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29813 q ha hb
  have h3 (q : Pattern) (ha : d148028 q = 1) (hb : d152145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148028, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148031 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148032 q = 1) (hb : d152146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148032, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148058 q = 1) (hb : d152147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148058, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148058, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148059 q = 1) (hb : d152148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148059, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148059, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148060 q = 1) (hb : d152741 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148060, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148060, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29983 (p : Pattern) (ha : d148148 p = 1) (hb : d152305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148106 q = 1) (hb : d152269 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28283 q ha hb
    | true =>
      simp only [d148106, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
  have h2 (q : Pattern) (ha : d148107 q = 1) (hb : d152270 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148108 q = 1) (hb : d152271 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148115 q = 1) (hb : d152273 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148115, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29843 q ha hb
  have h5 (q : Pattern) (ha : d148116 q = 1) (hb : d152274 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148117 q = 1) (hb : d152275 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148118 q = 1) (hb : d152276 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148118, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148134 q = 1) (hb : d152290 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148134, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28284 q ha hb
    | true =>
      simp only [d148134, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29847 q hb ha
  have h9 (q : Pattern) (ha : d148135 q = 1) (hb : d152291 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148135, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148135, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148136 q = 1) (hb : d152292 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148136, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148136, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148137 q = 1) (hb : d152293 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148137, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148137, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148147 q = 1) (hb : d152304 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148147, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148147, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148148 q = 1) (hb : d152305 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148148, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148148, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29984 (p : Pattern) (ha : d148154 p = 1) (hb : d152750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148149 q = 1) (hb : d152306 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148149, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29983 q ha hb
    | true =>
      simp only [d148149, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148150 q = 1) (hb : d152307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148150, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148150, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148140 q = 1) (hb : d152296 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29848 q ha hb
    | true =>
      simp only [d148140, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148141 q = 1) (hb : d152297 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148151 q = 1) (hb : d152747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148151, d152747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148151, d152747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148152 q = 1) (hb : d152748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148152, d152748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148152, d152748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148153 q = 1) (hb : d152749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148153, d152749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148153, d152749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148154 q = 1) (hb : d152750 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148154, d152750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148154, d152750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29985 (p : Pattern) (ha : d148179 p = 1) (hb : d152756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148159 q = 1) (hb : d152751 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148159, d152751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29984 q ha hb
    | true =>
      simp only [d148159, d152751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29854 q ha hb
  have h3 (q : Pattern) (ha : d148160 q = 1) (hb : d152752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148160, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148160, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148175 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148176 q = 1) (hb : d152753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148176, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148176, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148177 q = 1) (hb : d152754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148177, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148177, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148178 q = 1) (hb : d152755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148178, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148178, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148179 q = 1) (hb : d152756 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148179, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148179, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29986 (p : Pattern) (ha : d148192 p = 1) (hb : d152762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148036 q = 1) (hb : d152150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148036, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29980 q ha hb
    | true =>
      simp only [d148036, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29981 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148055 q = 1) (hb : d152151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148055, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148055, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148056 q = 1) (hb : d152739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148056, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148056, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148057 q = 1) (hb : d152740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148057, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148057, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148061 q = 1) (hb : d152742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148061, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148061, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29982 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d148063 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148064 q = 1) (hb : d152743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148064, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148064, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d148065 q = 1) (hb : d152744 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148065, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148065, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d148066 q = 1) (hb : d152745 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148066, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148066, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d148067 q = 1) (hb : d152746 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148067, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148067, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148180 q = 1) (hb : d152757 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148180, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148180, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29985 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148187 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148188 q = 1) (hb : d152758 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148188, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148188, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148189 q = 1) (hb : d152759 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148189, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148189, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d148190 q = 1) (hb : d152760 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148190, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148190, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d148191 q = 1) (hb : d152761 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148191, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148191, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d148192 q = 1) (hb : d152762 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148192, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148192, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29987 (p : Pattern) (ha : d148198 p = 1) (hb : d152768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148193 q = 1) (hb : d152763 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148193, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148193, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29986 q ha hb
  have h2 (q : Pattern) (ha : d148194 q = 1) (hb : d152764 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148194, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148194, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148195 q = 1) (hb : d152765 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148195, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148195, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148196 q = 1) (hb : d152766 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148196, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148196, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148197 q = 1) (hb : d152767 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148197, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148197, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148198 q = 1) (hb : d152768 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148198, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148198, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29988 (p : Pattern) (ha : d148332 p = 1) (hb : d152378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148275 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148312 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d148249 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29863 q ha hb
    | true =>
      simp only [d148249, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29864 q ha hb
  have h5 (q : Pattern) (ha : d148313 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d148313, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d148328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148329 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148329, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148330 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148330, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148331 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148331, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148332 q = 1) (hb : d152378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148332, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148332, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29989 (p : Pattern) (ha : d148354 p = 1) (hb : d152388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148249 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29863 q ha hb
    | true =>
      simp only [d148249, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29864 q ha hb
  have h4 (q : Pattern) (ha : d148313 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148313, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148328 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148329 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148329, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148330 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148330, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148331 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148331, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148338 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148343 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d148346 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d148259 q = 1) (hb : d152383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29866 q ha hb
    | true =>
      simp only [d148259, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29867 q ha hb
  have h13 (q : Pattern) (ha : d148347 q = 1) (hb : d152384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d148347, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148350 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148351 q = 1) (hb : d152385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148351, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148352 q = 1) (hb : d152386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148352, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d148352, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148353 q = 1) (hb : d152387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148353, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148353, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148354 q = 1) (hb : d152388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148354, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148354, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29990 (p : Pattern) (ha : d148379 p = 1) (hb : d152775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148346 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148259 q = 1) (hb : d152383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29866 q ha hb
    | true =>
      simp only [d148259, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29867 q ha hb
  have h3 (q : Pattern) (ha : d148347 q = 1) (hb : d152384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148347, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148350 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148351 q = 1) (hb : d152385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148351, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148377 q = 1) (hb : d152386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148377, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148377, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148378 q = 1) (hb : d152387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148378, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148378, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148379 q = 1) (hb : d152775 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148379, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148379, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29991 (p : Pattern) (ha : d148448 p = 1) (hb : d152542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148406 q = 1) (hb : d152506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28333 q ha hb
    | true =>
      simp only [d148406, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
  have h2 (q : Pattern) (ha : d148407 q = 1) (hb : d152507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148408 q = 1) (hb : d152508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148415 q = 1) (hb : d152510 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148415, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29896 q ha hb
  have h5 (q : Pattern) (ha : d148416 q = 1) (hb : d152511 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148417 q = 1) (hb : d152512 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148418 q = 1) (hb : d152513 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148418, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148434 q = 1) (hb : d152527 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148434, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28334 q ha hb
    | true =>
      simp only [d148434, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29900 q hb ha
  have h9 (q : Pattern) (ha : d148435 q = 1) (hb : d152528 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148435, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148435, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148436 q = 1) (hb : d152529 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148436, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148436, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148437 q = 1) (hb : d152530 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148437, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148437, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148447 q = 1) (hb : d152541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148447, d152541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148447, d152541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148448 q = 1) (hb : d152542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148448, d152542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148448, d152542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29992 (p : Pattern) (ha : d148454 p = 1) (hb : d152784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148449 q = 1) (hb : d152543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148449, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29991 q ha hb
    | true =>
      simp only [d148449, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148450 q = 1) (hb : d152544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148450, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148450, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148440 q = 1) (hb : d152533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29901 q ha hb
    | true =>
      simp only [d148440, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148441 q = 1) (hb : d152534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148451 q = 1) (hb : d152781 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148451, d152781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148451, d152781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148452 q = 1) (hb : d152782 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148452, d152782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148452, d152782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148453 q = 1) (hb : d152783 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148453, d152783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148453, d152783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148454 q = 1) (hb : d152784 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148454, d152784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148454, d152784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29993 (p : Pattern) (ha : d148479 p = 1) (hb : d152790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148446 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148459 q = 1) (hb : d152785 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148459, d152785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29992 q ha hb
    | true =>
      simp only [d148459, d152785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29907 q ha hb
  have h3 (q : Pattern) (ha : d148460 q = 1) (hb : d152786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148460, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148460, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148475 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148476 q = 1) (hb : d152787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148476, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148476, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148477 q = 1) (hb : d152788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148477, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148477, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148478 q = 1) (hb : d152789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148478, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148478, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148479 q = 1) (hb : d152790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148479, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148479, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29994 (p : Pattern) (ha : d148492 p = 1) (hb : d152796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148267 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148355 q = 1) (hb : d152389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148355, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29988 q ha hb
    | true =>
      simp only [d148355, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29989 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148373 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148374 q = 1) (hb : d152390 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148374, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148374, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148375 q = 1) (hb : d152773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148375, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148375, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148376 q = 1) (hb : d152774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148376, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148376, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148380 q = 1) (hb : d152776 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148380, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148380, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29990 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d148382 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148383 q = 1) (hb : d152777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148383, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148383, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d148384 q = 1) (hb : d152778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148384, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148384, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d148385 q = 1) (hb : d152779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148385, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148385, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d148386 q = 1) (hb : d152780 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148386, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148386, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148480 q = 1) (hb : d152791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148480, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148480, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29993 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148487 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148488 q = 1) (hb : d152792 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148488, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148488, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148489 q = 1) (hb : d152793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148489, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148489, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d148490 q = 1) (hb : d152794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148490, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148490, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d148491 q = 1) (hb : d152795 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148491, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148491, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d148492 q = 1) (hb : d152796 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148492, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148492, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29995 (p : Pattern) (ha : d148498 p = 1) (hb : d152802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148493 q = 1) (hb : d152797 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148493, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148493, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29994 q ha hb
  have h2 (q : Pattern) (ha : d148494 q = 1) (hb : d152798 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148494, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148494, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148495 q = 1) (hb : d152799 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148495, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148495, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148496 q = 1) (hb : d152800 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148496, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148496, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148497 q = 1) (hb : d152801 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148497, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148497, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148498 q = 1) (hb : d152802 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148498, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148498, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29996 (p : Pattern) (ha : d148504 p = 1) (hb : d152808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d147261 q = 1) (hb : d152677 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147261, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29959 q ha hb
    | true =>
      simp only [d147261, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29965 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147500 q = 1) (hb : d152704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147500, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147500, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29971 q ha hb
  have h3 (q : Pattern) (ha : d147501 q = 1) (hb : d152705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147501, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147501, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147858 q = 1) (hb : d152736 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147858, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147858, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29979 q ha hb
  have h5 (q : Pattern) (ha : d147859 q = 1) (hb : d152737 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147859, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147859, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147860 q = 1) (hb : d152738 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d147860, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147860, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148199 q = 1) (hb : d152769 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148199, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148199, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29987 q ha hb
  have h8 (q : Pattern) (ha : d148200 q = 1) (hb : d152770 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148200, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148200, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148201 q = 1) (hb : d152771 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148201, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148201, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148202 q = 1) (hb : d152772 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148202, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148202, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148499 q = 1) (hb : d152803 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148499, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148499, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29995 q ha hb
  have h12 (q : Pattern) (ha : d148500 q = 1) (hb : d152804 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148500, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148500, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148501 q = 1) (hb : d152805 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148501, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148501, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148502 q = 1) (hb : d152806 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148502, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148502, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148503 q = 1) (hb : d152807 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d148503, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148503, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148504 q = 1) (hb : d152808 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d148504, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148504, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro29997 (p : Pattern) (ha : d148510 p = 1) (hb : d152814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148505 q = 1) (hb : d152809 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d148505, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29996 q ha hb
    | true =>
      simp only [d148505, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148506 q = 1) (hb : d152810 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d148506, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148506, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148507 q = 1) (hb : d152811 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d148507, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148507, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148508 q = 1) (hb : d152812 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d148508, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148508, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148509 q = 1) (hb : d152813 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d148509, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148509, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148510 q = 1) (hb : d152814 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d148510, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148510, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29998 (p : Pattern) (ha : d148516 p = 1) (hb : d152820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148511 q = 1) (hb : d152815 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d148511, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29997 q ha hb
    | true =>
      simp only [d148511, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148512 q = 1) (hb : d152816 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d148512, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148512, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148513 q = 1) (hb : d152817 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d148513, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148513, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148514 q = 1) (hb : d152818 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d148514, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148514, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148515 q = 1) (hb : d152819 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d148515, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148515, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148516 q = 1) (hb : d152820 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d148516, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148516, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29999 (p : Pattern) (ha : d148522 p = 1) (hb : d152826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148517 q = 1) (hb : d152821 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d148517, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29998 q ha hb
    | true =>
      simp only [d148517, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148518 q = 1) (hb : d152822 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d148518, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148518, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148519 q = 1) (hb : d152823 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d148519, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148519, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148520 q = 1) (hb : d152824 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d148520, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148520, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148521 q = 1) (hb : d152825 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d148521, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148521, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148522 q = 1) (hb : d152826 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d148522, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148522, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
end NetHack.Soko22Hazard87
