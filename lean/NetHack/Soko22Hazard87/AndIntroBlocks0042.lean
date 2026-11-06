import NetHack.Soko22Hazard87.AndIntroBlocks0041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro10500 (p : Pattern) (ha : d6641 p = 1) (hb : d85724 p = 1) : d89011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2373 q = 1) (hb : d85723 q = 1) : d89006 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2373, d89006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10499 q ha hb
    | true =>
      simp only [d2373, d89006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2374 q = 1) (hb : d85723 q = 1) : d89007 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, d89007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2374, d89007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6638 q = 1) (hb : d85724 q = 1) : d89008 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6638, d85724, d89008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6638, d85724, d89008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6639 q = 1) (hb : d85724 q = 1) : d89009 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6639, d89009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6639, d89009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6640 q = 1) (hb : d85724 q = 1) : d89010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6640, d89010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6640, d89010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6641 q = 1) (hb : d85724 q = 1) : d89011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6641, d89011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6641, d89011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10501 (p : Pattern) (ha : d6654 p = 1) (hb : d85723 p = 1) : d89017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2370 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d6642 q = 1) : d6642 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6648 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6649 q = 1) (hb : d85721 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d85721, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d6649, d85721, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6650 q = 1) (hb : d85721 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6650, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6651 q = 1) (hb : d85721 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6651, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6652 q = 1) (hb : d85721 q = 1) : d89015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6652, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d6653 q = 1) (hb : d85723 q = 1) : d89016 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6653, d85723, d89016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6653, d85723, d89016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6654 q = 1) (hb : d85723 q = 1) : d89017 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6654, d89017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6654, d89017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10502 (p : Pattern) (ha : d6660 p = 1) (hb : d85724 p = 1) : d89023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6655 q = 1) (hb : d85723 q = 1) : d89018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6655, d89018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10501 q ha hb
    | true =>
      simp only [d6655, d89018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6656 q = 1) (hb : d85723 q = 1) : d89019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6656, d89019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6656, d89019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6657 q = 1) (hb : d85724 q = 1) : d89020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6657, d85724, d89020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6657, d85724, d89020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6658 q = 1) (hb : d85724 q = 1) : d89021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6658, d89021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6658, d89021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6659 q = 1) (hb : d85724 q = 1) : d89022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6659, d89022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6659, d89022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6660 q = 1) (hb : d85724 q = 1) : d89023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6660, d89023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6660, d89023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10503 (p : Pattern) (ha : d2377 p = 1) (hb : d85723 p = 1) : d89027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2370 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2356 q = 1) : d2356 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2366 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2367 q = 1) (hb : d85721 q = 1) : d12084 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2368 q = 1) (hb : d85721 q = 1) : d12085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2369 q = 1) (hb : d85721 q = 1) : d12086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2375 q = 1) (hb : d85721 q = 1) : d12092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d12092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2375, d12092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2376 q = 1) (hb : d85723 q = 1) : d89026 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2376, d85723, d89026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2376, d85723, d89026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2377 q = 1) (hb : d85723 q = 1) : d89027 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2377, d89027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2377, d89027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10504 (p : Pattern) (ha : d6671 p = 1) (hb : d85724 p = 1) : d89033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d85723 q = 1) : d89028 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d89028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10503 q ha hb
    | true =>
      simp only [d2378, d89028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d85723 q = 1) : d89029 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d89029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d89029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6668 q = 1) (hb : d85724 q = 1) : d89030 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6668, d85724, d89030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6668, d85724, d89030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6669 q = 1) (hb : d85724 q = 1) : d89031 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6669, d89031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6669, d89031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6670 q = 1) (hb : d85724 q = 1) : d89032 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6670, d89032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6670, d89032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6671 q = 1) (hb : d85724 q = 1) : d89033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6671, d89033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6671, d89033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10505 (p : Pattern) (ha : d77052 p = 1) (hb : d85724 p = 1) : d89039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6661 q = 1) (hb : d85724 q = 1) : d89024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6661, d89024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10500 q ha hb
    | true =>
      simp only [d6661, d89024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10502 q ha hb
  have h2 (q : Pattern) (ha : d77048 q = 1) (hb : d85724 q = 1) : d89025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77048, d89025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77048, d89025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6672 q = 1) (hb : d85724 q = 1) : d89034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10504 q ha hb
    | true =>
      simp only [d6672, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6673 q = 1) (hb : d85724 q = 1) : d89035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, d89035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6673, d89035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77049 q = 1) (hb : d85724 q = 1) : d89036 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77049, d89036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77049, d89036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77050 q = 1) (hb : d85724 q = 1) : d89037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77050, d89037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77050, d89037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77051 q = 1) (hb : d85724 q = 1) : d89038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77051, d89038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77051, d89038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77052 q = 1) (hb : d85724 q = 1) : d89039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77052, d89039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77052, d89039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10506 (p : Pattern) (ha : d77058 p = 1) (hb : d85724 p = 1) : d89045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6557 q = 1) (hb : d85724 q = 1) : d88916 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6557, d88916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6557, d88916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10478 q ha hb
  have h2 (q : Pattern) (ha : d6558 q = 1) (hb : d85724 q = 1) : d88917 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6558, d88917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6558, d88917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6566 q = 1) (hb : d85724 q = 1) : d88925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10478 q ha hb
    | true =>
      simp only [d6566, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10480 q ha hb
  have h4 (q : Pattern) (ha : d6567 q = 1) (hb : d85724 q = 1) : d88926 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6567, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6568 q = 1) (hb : d85724 q = 1) : d88927 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6568, d88927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6568, d88927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77036 q = 1) (hb : d85724 q = 1) : d88985 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77036, d88985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10490 q ha hb
    | true =>
      simp only [d77036, d88985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10497 q ha hb
  have h7 (q : Pattern) (ha : d6626 q = 1) (hb : d85724 q = 1) : d88992 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6626, d88992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10483 q ha hb
    | true =>
      simp only [d6626, d88992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10471 q ha hb
  have h8 (q : Pattern) (ha : d77037 q = 1) (hb : d85724 q = 1) : d88993 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77037, d88993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77037, d88993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77038 q = 1) (hb : d85724 q = 1) : d88994 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77038, d88994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77038, d88994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d77039 q = 1) (hb : d85724 q = 1) : d88995 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77039, d88995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77039, d88995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77043 q = 1) (hb : d85724 q = 1) : d88999 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77043, d88999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77043, d88999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10498 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10472 q ha hb
  have h13 (q : Pattern) (ha : d77044 q = 1) (hb : d85724 q = 1) : d89000 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77044, d89000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77044, d89000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77045 q = 1) (hb : d85724 q = 1) : d89001 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77045, d89001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77045, d89001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d77046 q = 1) (hb : d85724 q = 1) : d89002 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77046, d89002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77046, d89002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77047 q = 1) (hb : d85724 q = 1) : d89003 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77047, d89003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77047, d89003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77053 q = 1) (hb : d85724 q = 1) : d89040 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77053, d89040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77053, d89040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10505 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10475 q ha hb
  have h19 (q : Pattern) (ha : d77054 q = 1) (hb : d85724 q = 1) : d89041 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77054, d89041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77054, d89041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77055 q = 1) (hb : d85724 q = 1) : d89042 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77055, d89042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d77055, d89042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d77056 q = 1) (hb : d85724 q = 1) : d89043 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77056, d89043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77056, d89043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d77057 q = 1) (hb : d85724 q = 1) : d89044 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77057, d89044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77057, d89044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d77058 q = 1) (hb : d85724 q = 1) : d89045 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77058, d89045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77058, d89045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10507 (p : Pattern) (ha : d77064 p = 1) (hb : d85724 p = 1) : d89051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77059 q = 1) (hb : d85724 q = 1) : d89046 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77059, d89046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77059, d89046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10506 q ha hb
  have h2 (q : Pattern) (ha : d77060 q = 1) (hb : d85724 q = 1) : d89047 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77060, d89047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77060, d89047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77061 q = 1) (hb : d85724 q = 1) : d89048 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77061, d89048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77061, d89048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77062 q = 1) (hb : d85724 q = 1) : d89049 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77062, d89049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77062, d89049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77063 q = 1) (hb : d85724 q = 1) : d89050 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77063, d89050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77063, d89050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77064 q = 1) (hb : d85724 q = 1) : d89051 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77064, d89051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77064, d89051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10508 (p : Pattern) (ha : d77070 p = 1) (hb : d85724 p = 1) : d89057 p = 1 := by
  have h0 (q : Pattern) (ha : d76899 q = 1) (hb : d85724 q = 1) : d88442 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76899, d88442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10307 q ha hb
    | true =>
      simp only [d76899, d88442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10347 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76939 q = 1) (hb : d85724 q = 1) : d88593 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76939, d88593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76939, d88593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10387 q ha hb
  have h3 (q : Pattern) (ha : d76940 q = 1) (hb : d85724 q = 1) : d88594 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76940, d88594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76940, d88594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76980 q = 1) (hb : d85724 q = 1) : d88745 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76980, d88745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76980, d88745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10427 q ha hb
  have h5 (q : Pattern) (ha : d76981 q = 1) (hb : d85724 q = 1) : d88746 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76981, d88746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76981, d88746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76982 q = 1) (hb : d85724 q = 1) : d88747 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76982, d88747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76982, d88747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77022 q = 1) (hb : d85724 q = 1) : d88898 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77022, d88898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77022, d88898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10467 q ha hb
  have h8 (q : Pattern) (ha : d77023 q = 1) (hb : d85724 q = 1) : d88899 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77023, d88899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77023, d88899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77024 q = 1) (hb : d85724 q = 1) : d88900 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77024, d88900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77024, d88900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77025 q = 1) (hb : d85724 q = 1) : d88901 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77025, d88901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77025, d88901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77065 q = 1) (hb : d85724 q = 1) : d89052 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77065, d89052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77065, d89052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10507 q ha hb
  have h12 (q : Pattern) (ha : d77066 q = 1) (hb : d85724 q = 1) : d89053 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77066, d89053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77066, d89053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77067 q = 1) (hb : d85724 q = 1) : d89054 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77067, d89054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77067, d89054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77068 q = 1) (hb : d85724 q = 1) : d89055 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77068, d89055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77068, d89055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77069 q = 1) (hb : d85724 q = 1) : d89056 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d77069, d89056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77069, d89056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77070 q = 1) (hb : d85724 q = 1) : d89057 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d77070, d89057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77070, d89057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro10509 (p : Pattern) (ha : d77076 p = 1) (hb : d85724 p = 1) : d89063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77071 q = 1) (hb : d85724 q = 1) : d89058 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d77071, d89058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10508 q ha hb
    | true =>
      simp only [d77071, d89058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77072 q = 1) (hb : d85724 q = 1) : d89059 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d77072, d89059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77072, d89059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77073 q = 1) (hb : d85724 q = 1) : d89060 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d77073, d89060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77073, d89060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77074 q = 1) (hb : d85724 q = 1) : d89061 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d77074, d89061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77074, d89061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77075 q = 1) (hb : d85724 q = 1) : d89062 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d77075, d89062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77075, d89062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77076 q = 1) (hb : d85724 q = 1) : d89063 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d77076, d89063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77076, d89063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10510 (p : Pattern) (ha : d77082 p = 1) (hb : d85724 p = 1) : d89069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77077 q = 1) (hb : d85724 q = 1) : d89064 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d77077, d89064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10509 q ha hb
    | true =>
      simp only [d77077, d89064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77078 q = 1) (hb : d85724 q = 1) : d89065 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d77078, d89065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77078, d89065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77079 q = 1) (hb : d85724 q = 1) : d89066 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d77079, d89066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77079, d89066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77080 q = 1) (hb : d85724 q = 1) : d89067 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d77080, d89067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77080, d89067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77081 q = 1) (hb : d85724 q = 1) : d89068 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d77081, d89068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77081, d89068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77082 q = 1) (hb : d85724 q = 1) : d89069 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d77082, d89069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77082, d89069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10511 (p : Pattern) (ha : d77088 p = 1) (hb : d85724 p = 1) : d89075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77083 q = 1) (hb : d85724 q = 1) : d89070 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d77083, d89070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10510 q ha hb
    | true =>
      simp only [d77083, d89070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77084 q = 1) (hb : d85724 q = 1) : d89071 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d77084, d89071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77084, d89071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77085 q = 1) (hb : d85724 q = 1) : d89072 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d77085, d89072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77085, d89072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77086 q = 1) (hb : d85724 q = 1) : d89073 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d77086, d89073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77086, d89073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77087 q = 1) (hb : d85724 q = 1) : d89074 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d77087, d89074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77087, d89074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77088 q = 1) (hb : d85724 q = 1) : d89075 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d77088, d89075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77088, d89075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10512 (p : Pattern) (ha : d77094 p = 1) (hb : d85724 p = 1) : d89081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77089 q = 1) (hb : d85724 q = 1) : d89076 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77089, d89076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10511 q ha hb
    | true =>
      simp only [d77089, d89076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77090 q = 1) (hb : d85724 q = 1) : d89077 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77090, d89077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77090, d89077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77091 q = 1) (hb : d85724 q = 1) : d89078 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77091, d89078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77091, d89078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77092 q = 1) (hb : d85724 q = 1) : d89079 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77092, d89079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77092, d89079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77093 q = 1) (hb : d85724 q = 1) : d89080 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77093, d89080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77093, d89080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77094 q = 1) (hb : d85724 q = 1) : d89081 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77094, d89081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77094, d89081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10513 (p : Pattern) (ha : d77100 p = 1) (hb : d85724 p = 1) : d89087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77095 q = 1) (hb : d85724 q = 1) : d89082 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77095, d89082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10512 q ha hb
    | true =>
      simp only [d77095, d89082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77096 q = 1) (hb : d85724 q = 1) : d89083 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77096, d89083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77096, d89083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77097 q = 1) (hb : d85724 q = 1) : d89084 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77097, d89084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77097, d89084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77098 q = 1) (hb : d85724 q = 1) : d89085 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77098, d89085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77098, d89085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77099 q = 1) (hb : d85724 q = 1) : d89086 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77099, d89086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77099, d89086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77100 q = 1) (hb : d85724 q = 1) : d89087 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77100, d89087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77100, d89087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10514 (p : Pattern) (ha : d77106 p = 1) (hb : d85724 p = 1) : d89093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77101 q = 1) (hb : d85724 q = 1) : d89088 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77101, d89088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10513 q ha hb
    | true =>
      simp only [d77101, d89088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77102 q = 1) (hb : d85724 q = 1) : d89089 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77102, d89089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77102, d89089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77103 q = 1) (hb : d85724 q = 1) : d89090 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77103, d89090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77103, d89090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77104 q = 1) (hb : d85724 q = 1) : d89091 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77104, d89091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77104, d89091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77105 q = 1) (hb : d85724 q = 1) : d89092 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77105, d89092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77105, d89092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77106 q = 1) (hb : d85724 q = 1) : d89093 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77106, d89093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77106, d89093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10515 (p : Pattern) (ha : d77112 p = 1) (hb : d85724 p = 1) : d89099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77107 q = 1) (hb : d85724 q = 1) : d89094 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77107, d89094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10514 q ha hb
    | true =>
      simp only [d77107, d89094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77108 q = 1) (hb : d85724 q = 1) : d89095 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77108, d89095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77108, d89095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77109 q = 1) (hb : d85724 q = 1) : d89096 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77109, d89096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77109, d89096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77110 q = 1) (hb : d85724 q = 1) : d89097 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77110, d89097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77110, d89097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77111 q = 1) (hb : d85724 q = 1) : d89098 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77111, d89098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77111, d89098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77112 q = 1) (hb : d85724 q = 1) : d89099 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77112, d89099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77112, d89099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10516 (p : Pattern) (ha : d87047 p = 1) (hb : d88140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32 q = 1) (hb : d87044 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d87044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32, d87044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d87045 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d87045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33, d87045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34 q = 1) (hb : d87046 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d87046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34, d87046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d87046 q = 1) (hb : d88139 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87047 q = 1) (hb : d88140 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87047, d88140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87047, d88140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro10517 (p : Pattern) (ha : d87053 p = 1) (hb : d88146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87048 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10516 q ha hb
    | true =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87049 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87050 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87051 q = 1) (hb : d88144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87051, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87051, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87052 q = 1) (hb : d88145 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87052, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87052, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87053 q = 1) (hb : d88146 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87053, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87053, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10518 (p : Pattern) (ha : d87059 p = 1) (hb : d88152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87054 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
    | true =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87055 q = 1) (hb : d88148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87055, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87055, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87056 q = 1) (hb : d88149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87056, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87056, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87057 q = 1) (hb : d88150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87057, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87057, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87058 q = 1) (hb : d88151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87058, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87058, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87059 q = 1) (hb : d88152 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87059, d88152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87059, d88152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10519 (p : Pattern) (ha : d87060 p = 1) (hb : d88153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87048 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10516 q ha hb
    | true =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87049 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87050 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87051 q = 1) (hb : d88144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87051, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87051, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87052 q = 1) (hb : d88145 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87052, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87052, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87060 q = 1) (hb : d88153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87060, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87060, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10520 (p : Pattern) (ha : d87066 p = 1) (hb : d88159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87054 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
    | true =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87055 q = 1) (hb : d88148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87055, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87055, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87056 q = 1) (hb : d88149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87056, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87056, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87057 q = 1) (hb : d88150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87057, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87057, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87058 q = 1) (hb : d88151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87058, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87058, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87061 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10519 q ha hb
    | true =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87062 q = 1) (hb : d88155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87062, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87062, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d87063 q = 1) (hb : d88156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87063, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87063, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d87064 q = 1) (hb : d88157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87064, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87064, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87065 q = 1) (hb : d88158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87065, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87065, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87066 q = 1) (hb : d88159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87066, d88159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87066, d88159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10521 (p : Pattern) (ha : d87071 p = 1) (hb : d88164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87061 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10519 q ha hb
    | true =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87062 q = 1) (hb : d88155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87062, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87062, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87063 q = 1) (hb : d88156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87063, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87063, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87064 q = 1) (hb : d88157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87064, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87064, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87065 q = 1) (hb : d88158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87065, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87065, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87071 q = 1) (hb : d88164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87071, d88164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87071, d88164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10522 (p : Pattern) (ha : d87080 p = 1) (hb : d88171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87079 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d72 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d73 q = 1) (hb : d87077 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d87077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d87077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d87078 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d87078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74, d87078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75 q = 1) (hb : d87079 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d87079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75, d87079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d87079 q = 1) (hb : d88170 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87080 q = 1) (hb : d88171 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87080, d88171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87080, d88171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro10523 (p : Pattern) (ha : d87086 p = 1) (hb : d88177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87081 q = 1) (hb : d88172 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87081, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10522 q ha hb
    | true =>
      simp only [d87081, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87082 q = 1) (hb : d88173 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87082, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87082, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87083 q = 1) (hb : d88174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87083, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87083, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87084 q = 1) (hb : d88175 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87084, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87084, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87085 q = 1) (hb : d88176 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87085, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87085, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87086 q = 1) (hb : d88177 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87086, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87086, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10524 (p : Pattern) (ha : d87092 p = 1) (hb : d88183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87087 q = 1) (hb : d88178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87087, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10523 q ha hb
    | true =>
      simp only [d87087, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87088 q = 1) (hb : d88179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87088, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87088, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87089 q = 1) (hb : d88180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87089, d88180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87089, d88180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87090 q = 1) (hb : d88181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87090, d88181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87090, d88181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87091 q = 1) (hb : d88182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87091, d88182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87091, d88182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87092 q = 1) (hb : d88183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87092, d88183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87092, d88183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10525 (p : Pattern) (ha : d87098 p = 1) (hb : d88189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87067 q = 1) (hb : d88160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87067, d88160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10518 q ha hb
    | true =>
      simp only [d87067, d88160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10520 q ha hb
  have h2 (q : Pattern) (ha : d87068 q = 1) (hb : d88161 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87068, d88161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87068, d88161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87069 q = 1) (hb : d88162 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87069, d88162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87069, d88162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87070 q = 1) (hb : d88163 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87070, d88163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87070, d88163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87072 q = 1) (hb : d88165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87072, d88165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87072, d88165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10521 q ha hb
  have h6 (q : Pattern) (ha : d87073 q = 1) (hb : d88166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87073, d88166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87073, d88166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87074 q = 1) (hb : d88167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87074, d88167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87074, d88167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d87075 q = 1) (hb : d88168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87075, d88168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87075, d88168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d87076 q = 1) (hb : d88169 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87076, d88169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87076, d88169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87093 q = 1) (hb : d88184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87093, d88184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87093, d88184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10524 q ha hb
  have h11 (q : Pattern) (ha : d87094 q = 1) (hb : d88185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87094, d88185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87094, d88185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d87095 q = 1) (hb : d88186 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87095, d88186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87095, d88186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d87096 q = 1) (hb : d88187 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87096, d88187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87096, d88187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87097 q = 1) (hb : d88188 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87097, d88188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87097, d88188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87098 q = 1) (hb : d88189 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87098, d88189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87098, d88189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10526 (p : Pattern) (ha : d87108 p = 1) (hb : d88199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87054 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
    | true =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87104 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87104, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87104, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87105 q = 1) (hb : d88196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87105, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87105, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87106 q = 1) (hb : d88197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87106, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87106, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87107 q = 1) (hb : d88198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87107, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87107, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87108 q = 1) (hb : d88199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87108, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87108, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10527 (p : Pattern) (ha : d87115 p = 1) (hb : d88206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87054 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
    | true =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87104 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87104, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87104, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87105 q = 1) (hb : d88196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87105, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87105, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87106 q = 1) (hb : d88197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87106, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87106, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87107 q = 1) (hb : d88198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87107, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87107, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87061 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10519 q ha hb
    | true =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87111 q = 1) (hb : d88202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87111, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87111, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87112 q = 1) (hb : d88203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87112, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87112, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d87113 q = 1) (hb : d88204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87113, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87113, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87114 q = 1) (hb : d88205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87114, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87114, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87115 q = 1) (hb : d88206 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87115, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87115, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10528 (p : Pattern) (ha : d87120 p = 1) (hb : d88211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87048 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10516 q ha hb
    | true =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87049 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87050 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87051 q = 1) (hb : d88144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87051, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87051, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87119 q = 1) (hb : d88210 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87119, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87119, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87120 q = 1) (hb : d88211 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87120, d88211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87120, d88211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10529 (p : Pattern) (ha : d87127 p = 1) (hb : d88218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87048 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10516 q ha hb
    | true =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87049 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87050 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87125 q = 1) (hb : d88216 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87125, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87125, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87126 q = 1) (hb : d88217 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87126, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87126, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87127 q = 1) (hb : d88218 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87127, d88218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87127, d88218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10530 (p : Pattern) (ha : d87134 p = 1) (hb : d88223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10649 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10650 q = 1) (hb : d87131 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d87131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10650, d87131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10651 q = 1) (hb : d87132 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d87132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10651, d87132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32 q = 1) (hb : d87044 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d87044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32, d87044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d87045 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d87045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33, d87045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10652 q = 1) (hb : d87133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d87133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10652, d87133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87133 q = 1) (hb : d88222 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87134 q = 1) (hb : d88223 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87134, d88223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87134, d88223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10531 (p : Pattern) (ha : d87140 p = 1) (hb : d88229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10530 q ha hb
    | true =>
      simp only [d87135, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87049 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87137 q = 1) (hb : d88226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87137, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87137, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87138 q = 1) (hb : d88227 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87138, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87138, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87139 q = 1) (hb : d88228 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87139, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87139, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87140 q = 1) (hb : d88229 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87140, d88229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87140, d88229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10532 (p : Pattern) (ha : d87146 p = 1) (hb : d88235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87121 q = 1) (hb : d88212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87121, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10528 q ha hb
    | true =>
      simp only [d87121, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87122 q = 1) (hb : d88213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87122, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87122, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87123 q = 1) (hb : d88214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87123, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87123, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87124 q = 1) (hb : d88215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87124, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87124, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87128 q = 1) (hb : d88219 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87128, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10529 q ha hb
    | true =>
      simp only [d87128, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87129 q = 1) (hb : d88220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87129, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87129, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87130 q = 1) (hb : d88221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87130, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87130, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d87141 q = 1) (hb : d88230 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87141, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10531 q ha hb
    | true =>
      simp only [d87141, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d87054 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d87142 q = 1) (hb : d88231 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87142, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87142, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d87054 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
    | true =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d87055 q = 1) (hb : d88148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87055, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87055, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d87143 q = 1) (hb : d88232 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87143, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87143, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d87144 q = 1) (hb : d88233 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87144, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87144, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d87145 q = 1) (hb : d88234 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87145, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87145, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87146 q = 1) (hb : d88235 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87146, d88235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87146, d88235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro10533 (p : Pattern) (ha : d87147 p = 1) (hb : d88236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87048 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10516 q ha hb
    | true =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87049 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87050 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87051 q = 1) (hb : d88144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87051, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87051, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87119 q = 1) (hb : d88210 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87119, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87119, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87147 q = 1) (hb : d88236 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87147, d88236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87147, d88236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10534 (p : Pattern) (ha : d87152 p = 1) (hb : d88241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87048 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10516 q ha hb
    | true =>
      simp only [d87048, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87049 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87049, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87050 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87050, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87125 q = 1) (hb : d88216 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87125, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87125, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87126 q = 1) (hb : d88217 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87126, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87126, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87152 q = 1) (hb : d88241 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87152, d88241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87152, d88241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10535 (p : Pattern) (ha : d87156 p = 1) (hb : d88245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10530 q ha hb
    | true =>
      simp only [d87135, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87049 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87137 q = 1) (hb : d88226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87137, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87137, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87138 q = 1) (hb : d88227 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87138, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87138, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87139 q = 1) (hb : d88228 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87139, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87139, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87156 q = 1) (hb : d88245 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87156, d88245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87156, d88245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10536 (p : Pattern) (ha : d87162 p = 1) (hb : d88251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87121 q = 1) (hb : d88212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87121, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10528 q ha hb
    | true =>
      simp only [d87121, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87122 q = 1) (hb : d88213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87122, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87122, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87123 q = 1) (hb : d88214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87123, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87123, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87124 q = 1) (hb : d88215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87124, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87124, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87128 q = 1) (hb : d88219 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87128, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10529 q ha hb
    | true =>
      simp only [d87128, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87129 q = 1) (hb : d88220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87129, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87129, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87130 q = 1) (hb : d88221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87130, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87130, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d87141 q = 1) (hb : d88230 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87141, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10531 q ha hb
    | true =>
      simp only [d87141, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d87054 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d87142 q = 1) (hb : d88231 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87142, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87142, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d87054 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
    | true =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d87055 q = 1) (hb : d88148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87055, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87055, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d87143 q = 1) (hb : d88232 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87143, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87143, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d87144 q = 1) (hb : d88233 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87144, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87144, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d87145 q = 1) (hb : d88234 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87145, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87145, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87148 q = 1) (hb : d88237 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87148, d88237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10533 q ha hb
    | true =>
      simp only [d87148, d88237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d87149 q = 1) (hb : d88238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87149, d88238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87149, d88238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87150 q = 1) (hb : d88239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87150, d88239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87150, d88239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d87151 q = 1) (hb : d88240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87151, d88240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87151, d88240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d87153 q = 1) (hb : d88242 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87153, d88242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10534 q ha hb
    | true =>
      simp only [d87153, d88242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d87154 q = 1) (hb : d88243 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87154, d88243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87154, d88243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d87155 q = 1) (hb : d88244 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87155, d88244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d87155, d88244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d87157 q = 1) (hb : d88246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87157, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10535 q ha hb
    | true =>
      simp only [d87157, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10519 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d87061 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d87158 q = 1) (hb : d88247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87158, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d87158, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d87061 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10519 q ha hb
    | true =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d87062 q = 1) (hb : d88155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87062, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d87062, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d87159 q = 1) (hb : d88248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87159, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d87159, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d87160 q = 1) (hb : d88249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87160, d88249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d87160, d88249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d87161 q = 1) (hb : d88250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87161, d88250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d87161, d88250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d87162 q = 1) (hb : d88251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87162, d88251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87162, d88251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro10537 (p : Pattern) (ha : d87164 p = 1) (hb : d88253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87054 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
    | true =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87104 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87104, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87104, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87105 q = 1) (hb : d88196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87105, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87105, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87106 q = 1) (hb : d88197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87106, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87106, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87107 q = 1) (hb : d88198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87107, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87107, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87164 q = 1) (hb : d88253 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87164, d88253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87164, d88253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10538 (p : Pattern) (ha : d87171 p = 1) (hb : d88260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87157 q = 1) (hb : d88246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87157, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10535 q ha hb
    | true =>
      simp only [d87157, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10519 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87061 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87158 q = 1) (hb : d88247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87158, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87158, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87061 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10519 q ha hb
    | true =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87062 q = 1) (hb : d88155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87062, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87062, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87159 q = 1) (hb : d88248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87159, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87159, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87169 q = 1) (hb : d88258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87169, d88258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87169, d88258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87170 q = 1) (hb : d88259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87170, d88259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87170, d88259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87171 q = 1) (hb : d88260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87171, d88260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87171, d88260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10539 (p : Pattern) (ha : d87180 p = 1) (hb : d88267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87179 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10686 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10687 q = 1) (hb : d87177 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d87177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10687, d87177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10688 q = 1) (hb : d87178 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d87178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10688, d87178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d72 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d73 q = 1) (hb : d87077 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d87077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d87077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d87078 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d87078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74, d87078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10689 q = 1) (hb : d87179 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d87179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10689, d87179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87179 q = 1) (hb : d88266 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87180 q = 1) (hb : d88267 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87180, d88267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87180, d88267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10540 (p : Pattern) (ha : d87186 p = 1) (hb : d88273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87181 q = 1) (hb : d88268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87181, d88268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10539 q ha hb
    | true =>
      simp only [d87181, d88268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87182 q = 1) (hb : d88269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87182, d88269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87182, d88269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87082 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87183 q = 1) (hb : d88270 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87183, d88270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87183, d88270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87184 q = 1) (hb : d88271 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87184, d88271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87184, d88271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87185 q = 1) (hb : d88272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87185, d88272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87185, d88272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87186 q = 1) (hb : d88273 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87186, d88273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87186, d88273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10541 (p : Pattern) (ha : d87192 p = 1) (hb : d88279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87187 q = 1) (hb : d88274 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87187, d88274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10540 q ha hb
    | true =>
      simp only [d87187, d88274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10523 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87087 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87188 q = 1) (hb : d88275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87188, d88275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87188, d88275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87087 q = 1) (hb : d88178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87087, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10523 q ha hb
    | true =>
      simp only [d87087, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87088 q = 1) (hb : d88179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87088, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87088, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87189 q = 1) (hb : d88276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87189, d88276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87189, d88276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87190 q = 1) (hb : d88277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87190, d88277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87190, d88277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87191 q = 1) (hb : d88278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87191, d88278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87191, d88278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87192 q = 1) (hb : d88279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87192, d88279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87192, d88279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10542 (p : Pattern) (ha : d87198 p = 1) (hb : d88285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87109 q = 1) (hb : d88200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87109, d88200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87109, d88200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10526 q ha hb
  have h2 (q : Pattern) (ha : d87110 q = 1) (hb : d88201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87110, d88201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87110, d88201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87116 q = 1) (hb : d88207 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87116, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10526 q ha hb
    | true =>
      simp only [d87116, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10527 q ha hb
  have h4 (q : Pattern) (ha : d87117 q = 1) (hb : d88208 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87117, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87117, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87118 q = 1) (hb : d88209 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87118, d88209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87118, d88209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87163 q = 1) (hb : d88252 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87163, d88252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10532 q ha hb
    | true =>
      simp only [d87163, d88252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10536 q ha hb
  have h7 (q : Pattern) (ha : d87165 q = 1) (hb : d88254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87165, d88254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10537 q ha hb
    | true =>
      simp only [d87165, d88254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d87166 q = 1) (hb : d88255 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87166, d88255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87166, d88255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87167 q = 1) (hb : d88256 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87167, d88256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87167, d88256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87168 q = 1) (hb : d88257 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87168, d88257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87168, d88257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87172 q = 1) (hb : d88261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87172, d88261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87172, d88261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10538 q ha hb
  have h12 (q : Pattern) (ha : d87173 q = 1) (hb : d88262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87173, d88262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87173, d88262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d87174 q = 1) (hb : d88263 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87174, d88263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87174, d88263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87175 q = 1) (hb : d88264 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87175, d88264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87175, d88264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87176 q = 1) (hb : d88265 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87176, d88265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87176, d88265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87193 q = 1) (hb : d88280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87193, d88280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87193, d88280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10541 q ha hb
  have h17 (q : Pattern) (ha : d87194 q = 1) (hb : d88281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87194, d88281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d87194, d88281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d87195 q = 1) (hb : d88282 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87195, d88282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87195, d88282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d87196 q = 1) (hb : d88283 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87196, d88283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d87196, d88283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d87197 q = 1) (hb : d88284 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87197, d88284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d87197, d88284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d87198 q = 1) (hb : d88285 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87198, d88285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87198, d88285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro10543 (p : Pattern) (ha : d87204 p = 1) (hb : d88291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87099 q = 1) (hb : d88190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87099, d88190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87099, d88190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10525 q ha hb
  have h2 (q : Pattern) (ha : d87100 q = 1) (hb : d88191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87100, d88191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87100, d88191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87101 q = 1) (hb : d88192 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87101, d88192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87101, d88192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87102 q = 1) (hb : d88193 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87102, d88193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87102, d88193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87103 q = 1) (hb : d88194 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87103, d88194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87103, d88194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87199 q = 1) (hb : d88286 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87199, d88286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87199, d88286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10542 q ha hb
  have h7 (q : Pattern) (ha : d87200 q = 1) (hb : d88287 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87200, d88287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87200, d88287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87201 q = 1) (hb : d88288 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87201, d88288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87201, d88288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87202 q = 1) (hb : d88289 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87202, d88289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87202, d88289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87203 q = 1) (hb : d88290 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87203, d88290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87203, d88290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87204 q = 1) (hb : d88291 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d87204, d88291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87204, d88291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10544 (p : Pattern) (ha : d87134 p = 1) (hb : d88293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10649 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10650 q = 1) (hb : d87131 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d87131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10650, d87131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10651 q = 1) (hb : d87132 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d87132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10651, d87132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87045 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10863 q = 1) (hb : d87133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d87133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10863, d87133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87133 q = 1) (hb : d88292 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87134 q = 1) (hb : d88293 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87134, d88293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87134, d88293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10545 (p : Pattern) (ha : d87140 p = 1) (hb : d88299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10544 q ha hb
    | true =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87049 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87137 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87138 q = 1) (hb : d88297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87138, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87138, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87139 q = 1) (hb : d88298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87139, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87139, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87140 q = 1) (hb : d88299 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87140, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87140, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10546 (p : Pattern) (ha : d87209 p = 1) (hb : d88305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87141 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87141, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10545 q ha hb
    | true =>
      simp only [d87141, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87205 q = 1) (hb : d88301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87205, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87205, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87206 q = 1) (hb : d88302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87206, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87206, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87207 q = 1) (hb : d88303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87207, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87207, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87208 q = 1) (hb : d88304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87208, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87208, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87209 q = 1) (hb : d88305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87209, d88305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87209, d88305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10547 (p : Pattern) (ha : d87156 p = 1) (hb : d88308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10544 q ha hb
    | true =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87049 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87137 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87138 q = 1) (hb : d88297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87138, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87138, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87139 q = 1) (hb : d88298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87139, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87139, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87156 q = 1) (hb : d88308 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87156, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87156, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10548 (p : Pattern) (ha : d87216 p = 1) (hb : d88314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87141 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87141, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10545 q ha hb
    | true =>
      simp only [d87141, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87205 q = 1) (hb : d88301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87205, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87205, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87206 q = 1) (hb : d88302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87206, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87206, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87207 q = 1) (hb : d88303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87207, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87207, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87208 q = 1) (hb : d88304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87208, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87208, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87060 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87157 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87157, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10547 q ha hb
    | true =>
      simp only [d87157, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87212 q = 1) (hb : d88310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87212, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87212, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87213 q = 1) (hb : d88311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87213, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87213, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d87214 q = 1) (hb : d88312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87214, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87214, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d87215 q = 1) (hb : d88313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87215, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87215, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d87216 q = 1) (hb : d88314 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87216, d88314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87216, d88314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro10549 (p : Pattern) (ha : d4818 p = 1) (hb : d51995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d143 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4818 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4818, d51995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4818, d51995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10550 (p : Pattern) (ha : d87134 p = 1) (hb : d88343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51995 q = 1) (hb : d88338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q hb ha
    | true =>
      simp only [d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87131 q = 1) (hb : d88339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d87131, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87131, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87132 q = 1) (hb : d88340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d87132, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87132, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87045 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87133 q = 1) (hb : d88341 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d87133, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87133, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87133 q = 1) (hb : d88342 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87134 q = 1) (hb : d88343 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87134, d88343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87134, d88343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10551 (p : Pattern) (ha : d87140 p = 1) (hb : d88349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88344 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10550 q ha hb
    | true =>
      simp only [d87135, d88344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88345 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87049 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87137 q = 1) (hb : d88346 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87137, d88346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87137, d88346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87138 q = 1) (hb : d88347 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87138, d88347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87138, d88347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87139 q = 1) (hb : d88348 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87139, d88348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87139, d88348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87140 q = 1) (hb : d88349 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87140, d88349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87140, d88349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10552 (p : Pattern) (ha : d87221 p = 1) (hb : d88319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10544 q ha hb
    | true =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87049 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87137 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87138 q = 1) (hb : d88297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87138, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87138, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87220 q = 1) (hb : d88318 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87220, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87220, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87221 q = 1) (hb : d88319 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87221, d88319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87221, d88319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10553 (p : Pattern) (ha : d87228 p = 1) (hb : d88326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10544 q ha hb
    | true =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87049 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87137 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87226 q = 1) (hb : d88324 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87226, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87226, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87227 q = 1) (hb : d88325 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87227, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87227, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87228 q = 1) (hb : d88326 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87228, d88326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87228, d88326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10554 (p : Pattern) (ha : d87235 p = 1) (hb : d88331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87234 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52123 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10742 q = 1) (hb : d52123 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10743 q = 1) (hb : d87232 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d87232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10743, d87232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10744 q = 1) (hb : d87233 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d87233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10744, d87233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10649 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10650 q = 1) (hb : d87131 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d87131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10650, d87131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10651 q = 1) (hb : d87132 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d87132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10651, d87132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10745 q = 1) (hb : d87234 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d87234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10745, d87234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87234 q = 1) (hb : d88330 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87235 q = 1) (hb : d88331 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87235, d88331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87235, d88331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10555 (p : Pattern) (ha : d87241 p = 1) (hb : d88337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87236 q = 1) (hb : d88332 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87236, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10554 q ha hb
    | true =>
      simp only [d87236, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87237 q = 1) (hb : d88333 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87237, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87237, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87136 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87238 q = 1) (hb : d88334 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87238, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87238, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87239 q = 1) (hb : d88335 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87239, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87239, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87240 q = 1) (hb : d88336 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87240, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87240, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87241 q = 1) (hb : d88337 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87241, d88337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87241, d88337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10556 (p : Pattern) (ha : d87247 p = 1) (hb : d88299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10544 q ha hb
    | true =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87244 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87244, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87244, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87245 q = 1) (hb : d88297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87245, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87245, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87246 q = 1) (hb : d88298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87246, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87246, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87247 q = 1) (hb : d88299 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87247, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87247, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10557 (p : Pattern) (ha : d87253 p = 1) (hb : d88356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87222 q = 1) (hb : d88320 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87222, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10552 q ha hb
    | true =>
      simp only [d87222, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87223 q = 1) (hb : d88321 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87223, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87223, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87224 q = 1) (hb : d88322 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87224, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87224, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87225 q = 1) (hb : d88323 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87225, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87225, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87229 q = 1) (hb : d88327 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87229, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10553 q ha hb
    | true =>
      simp only [d87229, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87230 q = 1) (hb : d88328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87230, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87230, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87231 q = 1) (hb : d88329 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87231, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87231, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87242 q = 1) (hb : d88350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87242, d88350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10555 q ha hb
    | true =>
      simp only [d87242, d88350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10551 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87141 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d87243 q = 1) (hb : d88351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87243, d88351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87243, d88351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d87248 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87248, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10556 q ha hb
    | true =>
      simp only [d87248, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87249 q = 1) (hb : d88352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87249, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87249, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87250 q = 1) (hb : d88353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87250, d88353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87250, d88353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87251 q = 1) (hb : d88354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87251, d88354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87251, d88354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d87252 q = 1) (hb : d88355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87252, d88355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87252, d88355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87253 q = 1) (hb : d88356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87253, d88356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87253, d88356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10558 (p : Pattern) (ha : d87156 p = 1) (hb : d88367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88344 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10550 q ha hb
    | true =>
      simp only [d87135, d88344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88345 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87049 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87137 q = 1) (hb : d88346 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87137, d88346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87137, d88346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87138 q = 1) (hb : d88347 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87138, d88347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87138, d88347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87139 q = 1) (hb : d88348 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87139, d88348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87139, d88348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87156 q = 1) (hb : d88367 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87156, d88367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87156, d88367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10559 (p : Pattern) (ha : d87254 p = 1) (hb : d88357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10544 q ha hb
    | true =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87049 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87137 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87138 q = 1) (hb : d88297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87138, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87138, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87220 q = 1) (hb : d88318 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87220, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87220, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87254 q = 1) (hb : d88357 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87254, d88357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87254, d88357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10560 (p : Pattern) (ha : d87259 p = 1) (hb : d88362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10544 q ha hb
    | true =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87049 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87137 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87137, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87226 q = 1) (hb : d88324 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87226, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87226, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87227 q = 1) (hb : d88325 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87227, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87227, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87259 q = 1) (hb : d88362 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87259, d88362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87259, d88362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10561 (p : Pattern) (ha : d87263 p = 1) (hb : d88366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87236 q = 1) (hb : d88332 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87236, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10554 q ha hb
    | true =>
      simp only [d87236, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87237 q = 1) (hb : d88333 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87237, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87237, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87136 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87238 q = 1) (hb : d88334 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87238, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87238, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87239 q = 1) (hb : d88335 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87239, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87239, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87240 q = 1) (hb : d88336 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87240, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87240, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87263 q = 1) (hb : d88366 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87263, d88366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87263, d88366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10562 (p : Pattern) (ha : d87266 p = 1) (hb : d88308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87135 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10544 q ha hb
    | true =>
      simp only [d87135, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87136 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87136, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87244 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87244, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87244, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87245 q = 1) (hb : d88297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87245, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87245, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87246 q = 1) (hb : d88298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87246, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87246, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87266 q = 1) (hb : d88308 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87266, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87266, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10563 (p : Pattern) (ha : d87272 p = 1) (hb : d88374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87222 q = 1) (hb : d88320 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87222, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10552 q ha hb
    | true =>
      simp only [d87222, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87223 q = 1) (hb : d88321 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87223, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87223, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87224 q = 1) (hb : d88322 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87224, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87224, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87225 q = 1) (hb : d88323 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87225, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87225, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87229 q = 1) (hb : d88327 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87229, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10553 q ha hb
    | true =>
      simp only [d87229, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87230 q = 1) (hb : d88328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87230, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87230, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87231 q = 1) (hb : d88329 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87231, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87231, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87242 q = 1) (hb : d88350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87242, d88350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10555 q ha hb
    | true =>
      simp only [d87242, d88350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10551 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87141 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d87243 q = 1) (hb : d88351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87243, d88351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87243, d88351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d87248 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87248, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10556 q ha hb
    | true =>
      simp only [d87248, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87249 q = 1) (hb : d88352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87249, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87249, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87250 q = 1) (hb : d88353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87250, d88353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87250, d88353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87251 q = 1) (hb : d88354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87251, d88354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87251, d88354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d87252 q = 1) (hb : d88355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87252, d88355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87252, d88355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d87147 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d87255 q = 1) (hb : d88358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87255, d88358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10559 q ha hb
    | true =>
      simp only [d87255, d88358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d87256 q = 1) (hb : d88359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87256, d88359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87256, d88359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d87257 q = 1) (hb : d88360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87257, d88360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d87257, d88360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d87258 q = 1) (hb : d88361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87258, d88361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87258, d88361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d87152 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d87260 q = 1) (hb : d88363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87260, d88363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10560 q ha hb
    | true =>
      simp only [d87260, d88363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d87261 q = 1) (hb : d88364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87261, d88364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87261, d88364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d87262 q = 1) (hb : d88365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87262, d88365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d87262, d88365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d87264 q = 1) (hb : d88368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87264, d88368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10561 q ha hb
    | true =>
      simp only [d87264, d88368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10558 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d87157 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d87265 q = 1) (hb : d88369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87265, d88369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d87265, d88369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d87267 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87267, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10562 q ha hb
    | true =>
      simp only [d87267, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d87268 q = 1) (hb : d88370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87268, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d87268, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d87269 q = 1) (hb : d88371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87269, d88371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d87269, d88371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d87270 q = 1) (hb : d88372 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87270, d88372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d87270, d88372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d87271 q = 1) (hb : d88373 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87271, d88373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d87271, d88373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d87272 q = 1) (hb : d88374 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87272, d88374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87272, d88374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro10564 (p : Pattern) (ha : d87274 p = 1) (hb : d88381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87141 q = 1) (hb : d88376 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87141, d88376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10551 q ha hb
    | true =>
      simp only [d87141, d88376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87205 q = 1) (hb : d88377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87205, d88377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87205, d88377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87206 q = 1) (hb : d88378 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87206, d88378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87206, d88378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87207 q = 1) (hb : d88379 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87207, d88379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87207, d88379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87208 q = 1) (hb : d88380 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87208, d88380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87208, d88380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87107 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87274 q = 1) (hb : d88381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87274, d88381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87274, d88381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10565 (p : Pattern) (ha : d87281 p = 1) (hb : d88388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87264 q = 1) (hb : d88368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87264, d88368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10561 q ha hb
    | true =>
      simp only [d87264, d88368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10558 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87265 q = 1) (hb : d88369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87265, d88369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87265, d88369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87267 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87267, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10562 q ha hb
    | true =>
      simp only [d87267, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87268 q = 1) (hb : d88370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87268, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87268, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87269 q = 1) (hb : d88371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87269, d88371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87269, d88371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87279 q = 1) (hb : d88386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87279, d88386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87279, d88386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87280 q = 1) (hb : d88387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87280, d88387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87280, d88387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87281 q = 1) (hb : d88388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87281, d88388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87281, d88388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10566 (p : Pattern) (ha : d6078 p = 1) (hb : d52049 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d230 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6078 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6078, d52049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6078, d52049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10567 (p : Pattern) (ha : d87180 p = 1) (hb : d88407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87179 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52049 q = 1) (hb : d88402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q hb ha
    | true =>
      simp only [d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87177 q = 1) (hb : d88403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d87177, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87177, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87178 q = 1) (hb : d88404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d87178, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87178, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87078 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87179 q = 1) (hb : d88405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d87179, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87179, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87179 q = 1) (hb : d88406 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87180 q = 1) (hb : d88407 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87180, d88407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87180, d88407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10568 (p : Pattern) (ha : d87186 p = 1) (hb : d88413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87181 q = 1) (hb : d88408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87181, d88408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10567 q ha hb
    | true =>
      simp only [d87181, d88408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87182 q = 1) (hb : d88409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87182, d88409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87182, d88409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87082 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87183 q = 1) (hb : d88410 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87183, d88410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87183, d88410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87184 q = 1) (hb : d88411 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87184, d88411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87184, d88411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87185 q = 1) (hb : d88412 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87185, d88412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87185, d88412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87186 q = 1) (hb : d88413 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87186, d88413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87186, d88413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10569 (p : Pattern) (ha : d87292 p = 1) (hb : d88395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87291 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52183 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10814 q = 1) (hb : d52183 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10815 q = 1) (hb : d87289 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d87289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10815, d87289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10816 q = 1) (hb : d87290 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d87290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10816, d87290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10686 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10687 q = 1) (hb : d87177 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d87177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10687, d87177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10688 q = 1) (hb : d87178 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d87178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10688, d87178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10817 q = 1) (hb : d87291 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d87291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10817, d87291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87291 q = 1) (hb : d88394 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87292 q = 1) (hb : d88395 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87292, d88395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87292, d88395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10570 (p : Pattern) (ha : d87298 p = 1) (hb : d88401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87293 q = 1) (hb : d88396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87293, d88396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10569 q ha hb
    | true =>
      simp only [d87293, d88396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87294 q = 1) (hb : d88397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87294, d88397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87294, d88397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87182 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87295 q = 1) (hb : d88398 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87295, d88398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87295, d88398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87296 q = 1) (hb : d88399 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87296, d88399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87296, d88399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87297 q = 1) (hb : d88400 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87297, d88400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87297, d88400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87298 q = 1) (hb : d88401 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87298, d88401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87298, d88401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10571 (p : Pattern) (ha : d87180 p = 1) (hb : d88417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87179 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10686 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10687 q = 1) (hb : d87177 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d87177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10687, d87177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10688 q = 1) (hb : d87178 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d87178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10688, d87178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87078 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11021 q = 1) (hb : d87179 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d87179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11021, d87179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87179 q = 1) (hb : d88416 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87180 q = 1) (hb : d88417 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87180, d88417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87180, d88417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10572 (p : Pattern) (ha : d87304 p = 1) (hb : d88423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87181 q = 1) (hb : d88418 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87181, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10571 q ha hb
    | true =>
      simp only [d87181, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87182 q = 1) (hb : d88419 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87182, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87182, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87301 q = 1) (hb : d88420 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87301, d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87301, d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87302 q = 1) (hb : d88421 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87302, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87302, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87303 q = 1) (hb : d88422 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87303, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87303, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87304 q = 1) (hb : d88423 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87304, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87304, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10573 (p : Pattern) (ha : d87310 p = 1) (hb : d88429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87299 q = 1) (hb : d88414 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87299, d88414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10570 q ha hb
    | true =>
      simp only [d87299, d88414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10568 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87187 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87300 q = 1) (hb : d88415 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87300, d88415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87300, d88415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87305 q = 1) (hb : d88424 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87305, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10572 q ha hb
    | true =>
      simp only [d87305, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87306 q = 1) (hb : d88425 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87306, d88425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87306, d88425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87307 q = 1) (hb : d88426 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87307, d88426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87307, d88426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87308 q = 1) (hb : d88427 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87308, d88427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87308, d88427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87309 q = 1) (hb : d88428 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87309, d88428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87309, d88428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87310 q = 1) (hb : d88429 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87310, d88429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87310, d88429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10574 (p : Pattern) (ha : d87322 p = 1) (hb : d88435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87210 q = 1) (hb : d88306 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87210, d88306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87210, d88306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10546 q ha hb
  have h2 (q : Pattern) (ha : d87211 q = 1) (hb : d88307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87211, d88307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87211, d88307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87217 q = 1) (hb : d88315 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87217, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10546 q ha hb
    | true =>
      simp only [d87217, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10548 q ha hb
  have h4 (q : Pattern) (ha : d87218 q = 1) (hb : d88316 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87218, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87218, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87219 q = 1) (hb : d88317 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87219, d88317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87219, d88317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87273 q = 1) (hb : d88375 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87273, d88375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10557 q ha hb
    | true =>
      simp only [d87273, d88375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10563 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87115 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87275 q = 1) (hb : d88382 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87275, d88382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10564 q ha hb
    | true =>
      simp only [d87275, d88382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87276 q = 1) (hb : d88383 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87276, d88383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87276, d88383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87277 q = 1) (hb : d88384 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87277, d88384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87277, d88384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d87278 q = 1) (hb : d88385 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87278, d88385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87278, d88385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d87282 q = 1) (hb : d88389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87282, d88389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87282, d88389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10565 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d87284 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d87285 q = 1) (hb : d88390 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87285, d88390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87285, d88390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d87286 q = 1) (hb : d88391 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87286, d88391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d87286, d88391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d87287 q = 1) (hb : d88392 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87287, d88392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87287, d88392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d87288 q = 1) (hb : d88393 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87288, d88393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87288, d88393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87311 q = 1) (hb : d88430 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87311, d88430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87311, d88430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10573 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d87317 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d87318 q = 1) (hb : d88431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87318, d88431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d87318, d88431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d87319 q = 1) (hb : d88432 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87319, d88432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d87319, d88432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d87320 q = 1) (hb : d88433 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87320, d88433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d87320, d88433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d87321 q = 1) (hb : d88434 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87321, d88434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d87321, d88434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d87322 q = 1) (hb : d88435 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87322, d88435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87322, d88435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro10575 (p : Pattern) (ha : d87328 p = 1) (hb : d88441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87323 q = 1) (hb : d88436 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87323, d88436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87323, d88436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10574 q ha hb
  have h2 (q : Pattern) (ha : d87324 q = 1) (hb : d88437 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87324, d88437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87324, d88437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87325 q = 1) (hb : d88438 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87325, d88438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87325, d88438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87326 q = 1) (hb : d88439 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87326, d88439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87326, d88439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87327 q = 1) (hb : d88440 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87327, d88440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87327, d88440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87328 q = 1) (hb : d88441 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d87328, d88441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87328, d88441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10576 (p : Pattern) (ha : d87335 p = 1) (hb : d88444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11099 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11100 q = 1) (hb : d87330 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d87330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11100, d87330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11101 q = 1) (hb : d87331 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d87331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11101, d87331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87333 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11103 q = 1) (hb : d87334 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d87334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11103, d87334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87334 q = 1) (hb : d88443 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87335 q = 1) (hb : d88444 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87335, d88444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87335, d88444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10577 (p : Pattern) (ha : d87345 p = 1) (hb : d88450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87336 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10576 q ha hb
    | true =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87337 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87342 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87343 q = 1) (hb : d88448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87343, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87343, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87344 q = 1) (hb : d88449 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87344, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87344, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87345 q = 1) (hb : d88450 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87345, d88450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87345, d88450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10578 (p : Pattern) (ha : d87355 p = 1) (hb : d88456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87350 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87350, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10577 q ha hb
    | true =>
      simp only [d87350, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87351 q = 1) (hb : d88452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87351, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87351, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87352 q = 1) (hb : d88453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87352, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87352, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87353 q = 1) (hb : d88454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87353, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87353, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87354 q = 1) (hb : d88455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87354, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87354, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87355 q = 1) (hb : d88456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87355, d88456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87355, d88456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10579 (p : Pattern) (ha : d87358 p = 1) (hb : d88459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87336 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10576 q ha hb
    | true =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87337 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87342 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87343 q = 1) (hb : d88448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87343, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87343, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87344 q = 1) (hb : d88449 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87344, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87344, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87358 q = 1) (hb : d88459 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87358, d88459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87358, d88459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10580 (p : Pattern) (ha : d87365 p = 1) (hb : d88465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87350 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87350, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10577 q ha hb
    | true =>
      simp only [d87350, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87351 q = 1) (hb : d88452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87351, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87351, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87352 q = 1) (hb : d88453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87352, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87352, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87353 q = 1) (hb : d88454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87353, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87353, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87354 q = 1) (hb : d88455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87354, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87354, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87359 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87360 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87360, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10579 q ha hb
    | true =>
      simp only [d87360, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87361 q = 1) (hb : d88461 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87361, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87361, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87362 q = 1) (hb : d88462 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87362, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87362, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d87363 q = 1) (hb : d88463 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87363, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87363, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d87364 q = 1) (hb : d88464 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87364, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87364, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d87365 q = 1) (hb : d88465 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87365, d88465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87365, d88465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro10581 (p : Pattern) (ha : d4913 p = 1) (hb : d52435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4913 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4913, d52435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4913, d52435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10582 (p : Pattern) (ha : d87335 p = 1) (hb : d88494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52435 q = 1) (hb : d88489 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10581 q hb ha
    | true =>
      simp only [d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87330 q = 1) (hb : d88490 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d87330, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87330, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87331 q = 1) (hb : d88491 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d87331, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87331, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87333 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87334 q = 1) (hb : d88492 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d87334, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87334, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87334 q = 1) (hb : d88493 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87335 q = 1) (hb : d88494 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87335, d88494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87335, d88494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10583 (p : Pattern) (ha : d87345 p = 1) (hb : d88500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87336 q = 1) (hb : d88495 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87336, d88495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10582 q ha hb
    | true =>
      simp only [d87336, d88495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87337 q = 1) (hb : d88496 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87337, d88496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87337, d88496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87342 q = 1) (hb : d88497 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87342, d88497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87342, d88497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87343 q = 1) (hb : d88498 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87343, d88498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87343, d88498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87344 q = 1) (hb : d88499 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87344, d88499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87344, d88499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87345 q = 1) (hb : d88500 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87345, d88500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87345, d88500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10584 (p : Pattern) (ha : d87370 p = 1) (hb : d88470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87336 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10576 q ha hb
    | true =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87337 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87342 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87343 q = 1) (hb : d88448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87343, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87343, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87369 q = 1) (hb : d88469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87369, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87369, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87370 q = 1) (hb : d88470 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87370, d88470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87370, d88470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10585 (p : Pattern) (ha : d87379 p = 1) (hb : d88477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87336 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10576 q ha hb
    | true =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87337 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87342 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87377 q = 1) (hb : d88475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87377, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87377, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87378 q = 1) (hb : d88476 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87378, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87378, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87379 q = 1) (hb : d88477 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87379, d88477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87379, d88477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10586 (p : Pattern) (ha : d87389 p = 1) (hb : d88482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52433 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11096 q = 1) (hb : d52433 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11097 q = 1) (hb : d87386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d87386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11097, d87386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11098 q = 1) (hb : d87387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d87387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11098, d87387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11099 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11100 q = 1) (hb : d87330 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d87330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11100, d87330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11101 q = 1) (hb : d87331 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d87331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11101, d87331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11102 q = 1) (hb : d87388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d87388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11102, d87388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87388 q = 1) (hb : d88481 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87389 q = 1) (hb : d88482 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87389, d88482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87389, d88482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10587 (p : Pattern) (ha : d87395 p = 1) (hb : d88488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87390 q = 1) (hb : d88483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87390, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10586 q ha hb
    | true =>
      simp only [d87390, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87391 q = 1) (hb : d88484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87391, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87391, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87337 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87392 q = 1) (hb : d88485 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87392, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87392, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87393 q = 1) (hb : d88486 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87393, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87393, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87394 q = 1) (hb : d88487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87394, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87394, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87395 q = 1) (hb : d88488 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87395, d88488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87395, d88488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10588 (p : Pattern) (ha : d87401 p = 1) (hb : d88450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87336 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10576 q ha hb
    | true =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87337 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87398 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87398, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87398, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87399 q = 1) (hb : d88448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87399, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87399, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87400 q = 1) (hb : d88449 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87400, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87400, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87401 q = 1) (hb : d88450 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87401, d88450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87401, d88450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10589 (p : Pattern) (ha : d87407 p = 1) (hb : d88507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87372 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87373 q = 1) (hb : d88471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87373, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10584 q ha hb
    | true =>
      simp only [d87373, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87374 q = 1) (hb : d88472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87374, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87374, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87375 q = 1) (hb : d88473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87375, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87375, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87376 q = 1) (hb : d88474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87376, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87376, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87382 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87383 q = 1) (hb : d88478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87383, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10585 q ha hb
    | true =>
      simp only [d87383, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87384 q = 1) (hb : d88479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87384, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87384, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87385 q = 1) (hb : d88480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87385, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87385, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87396 q = 1) (hb : d88501 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87396, d88501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10587 q ha hb
    | true =>
      simp only [d87396, d88501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10583 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87350 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d87397 q = 1) (hb : d88502 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87397, d88502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87397, d88502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d87402 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87402, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10588 q ha hb
    | true =>
      simp only [d87402, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87403 q = 1) (hb : d88503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87403, d88503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87403, d88503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87404 q = 1) (hb : d88504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87404, d88504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87404, d88504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87405 q = 1) (hb : d88505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87405, d88505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87405, d88505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d87406 q = 1) (hb : d88506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87406, d88506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87406, d88506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87407 q = 1) (hb : d88507 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87407, d88507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87407, d88507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10590 (p : Pattern) (ha : d87358 p = 1) (hb : d88518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87336 q = 1) (hb : d88495 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87336, d88495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10582 q ha hb
    | true =>
      simp only [d87336, d88495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87337 q = 1) (hb : d88496 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87337, d88496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87337, d88496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87342 q = 1) (hb : d88497 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87342, d88497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87342, d88497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87343 q = 1) (hb : d88498 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87343, d88498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87343, d88498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87344 q = 1) (hb : d88499 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87344, d88499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87344, d88499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87358 q = 1) (hb : d88518 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87358, d88518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87358, d88518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10591 (p : Pattern) (ha : d87408 p = 1) (hb : d88508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87336 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10576 q ha hb
    | true =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87337 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87342 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87343 q = 1) (hb : d88448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87343, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87343, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87369 q = 1) (hb : d88469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87369, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87369, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87408 q = 1) (hb : d88508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87408, d88508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87408, d88508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10592 (p : Pattern) (ha : d87414 p = 1) (hb : d88513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87336 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10576 q ha hb
    | true =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87337 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87342 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87342, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87377 q = 1) (hb : d88475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87377, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87377, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87378 q = 1) (hb : d88476 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87378, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87378, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87414 q = 1) (hb : d88513 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87414, d88513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87414, d88513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10593 (p : Pattern) (ha : d87419 p = 1) (hb : d88517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87390 q = 1) (hb : d88483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87390, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10586 q ha hb
    | true =>
      simp only [d87390, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87391 q = 1) (hb : d88484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87391, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87391, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87337 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87392 q = 1) (hb : d88485 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87392, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87392, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87393 q = 1) (hb : d88486 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87393, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87393, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87394 q = 1) (hb : d88487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87394, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87394, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87419 q = 1) (hb : d88517 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87419, d88517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87419, d88517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10594 (p : Pattern) (ha : d87422 p = 1) (hb : d88459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87336 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10576 q ha hb
    | true =>
      simp only [d87336, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87337 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87337, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87398 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87398, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87398, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87399 q = 1) (hb : d88448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87399, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87399, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87400 q = 1) (hb : d88449 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87400, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87400, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87422 q = 1) (hb : d88459 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87422, d88459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87422, d88459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10595 (p : Pattern) (ha : d87428 p = 1) (hb : d88525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87372 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87373 q = 1) (hb : d88471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87373, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10584 q ha hb
    | true =>
      simp only [d87373, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87374 q = 1) (hb : d88472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87374, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87374, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87375 q = 1) (hb : d88473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87375, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87375, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87376 q = 1) (hb : d88474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87376, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87376, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87382 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87383 q = 1) (hb : d88478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87383, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10585 q ha hb
    | true =>
      simp only [d87383, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87384 q = 1) (hb : d88479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87384, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87384, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87385 q = 1) (hb : d88480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87385, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87385, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87396 q = 1) (hb : d88501 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87396, d88501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10587 q ha hb
    | true =>
      simp only [d87396, d88501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10583 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87350 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d87397 q = 1) (hb : d88502 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87397, d88502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87397, d88502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d87402 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87402, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10588 q ha hb
    | true =>
      simp only [d87402, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87403 q = 1) (hb : d88503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87403, d88503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87403, d88503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87404 q = 1) (hb : d88504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87404, d88504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87404, d88504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87405 q = 1) (hb : d88505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87405, d88505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87405, d88505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d87406 q = 1) (hb : d88506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87406, d88506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87406, d88506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d87409 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d87410 q = 1) (hb : d88509 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87410, d88509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10591 q ha hb
    | true =>
      simp only [d87410, d88509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d87411 q = 1) (hb : d88510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87411, d88510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87411, d88510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d87412 q = 1) (hb : d88511 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87412, d88511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d87412, d88511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d87413 q = 1) (hb : d88512 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87413, d88512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87413, d88512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d87415 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d87416 q = 1) (hb : d88514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87416, d88514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10592 q ha hb
    | true =>
      simp only [d87416, d88514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d87417 q = 1) (hb : d88515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87417, d88515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87417, d88515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d87418 q = 1) (hb : d88516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87418, d88516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d87418, d88516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d87420 q = 1) (hb : d88519 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87420, d88519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10593 q ha hb
    | true =>
      simp only [d87420, d88519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10590 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d87360 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d87421 q = 1) (hb : d88520 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87421, d88520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d87421, d88520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d87423 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87423, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10594 q ha hb
    | true =>
      simp only [d87423, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d87424 q = 1) (hb : d88521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87424, d88521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d87424, d88521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d87425 q = 1) (hb : d88522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87425, d88522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d87425, d88522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d87426 q = 1) (hb : d88523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87426, d88523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d87426, d88523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d87427 q = 1) (hb : d88524 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87427, d88524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d87427, d88524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d87428 q = 1) (hb : d88525 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87428, d88525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87428, d88525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro10596 (p : Pattern) (ha : d87435 p = 1) (hb : d88532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87350 q = 1) (hb : d88527 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87350, d88527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10583 q ha hb
    | true =>
      simp only [d87350, d88527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87351 q = 1) (hb : d88528 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87351, d88528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87351, d88528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87352 q = 1) (hb : d88529 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87352, d88529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87352, d88529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87353 q = 1) (hb : d88530 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87353, d88530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87353, d88530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87354 q = 1) (hb : d88531 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87354, d88531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87354, d88531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87434 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87435 q = 1) (hb : d88532 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87435, d88532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87435, d88532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10597 (p : Pattern) (ha : d87448 p = 1) (hb : d88539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87420 q = 1) (hb : d88519 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87420, d88519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10593 q ha hb
    | true =>
      simp only [d87420, d88519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10590 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87421 q = 1) (hb : d88520 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87421, d88520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87421, d88520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87423 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87423, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10594 q ha hb
    | true =>
      simp only [d87423, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87424 q = 1) (hb : d88521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87424, d88521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87424, d88521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87425 q = 1) (hb : d88522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87425, d88522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87425, d88522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87446 q = 1) (hb : d88537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87446, d88537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87446, d88537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87447 q = 1) (hb : d88538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87447, d88538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87447, d88538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87448 q = 1) (hb : d88539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87448, d88539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87448, d88539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10598 (p : Pattern) (ha : d87461 p = 1) (hb : d88546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87460 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52595 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11267 q = 1) (hb : d52595 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11268 q = 1) (hb : d87456 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d87456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11268, d87456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11269 q = 1) (hb : d87457 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d87457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11269, d87457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11271 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11272 q = 1) (hb : d87458 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d87458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11272, d87458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11273 q = 1) (hb : d87459 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d87459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11273, d87459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11274 q = 1) (hb : d87460 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d87460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11274, d87460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87460 q = 1) (hb : d88545 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87461 q = 1) (hb : d88546 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87461, d88546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87461, d88546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10599 (p : Pattern) (ha : d87473 p = 1) (hb : d88552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87462 q = 1) (hb : d88547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87462, d88547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10598 q ha hb
    | true =>
      simp only [d87462, d88547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87463 q = 1) (hb : d88548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87463, d88548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87463, d88548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87469 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87470 q = 1) (hb : d88549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87470, d88549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87470, d88549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87471 q = 1) (hb : d88550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87471, d88550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87471, d88550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87472 q = 1) (hb : d88551 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87472, d88551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87472, d88551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87473 q = 1) (hb : d88552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87473, d88552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87473, d88552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10600 (p : Pattern) (ha : d6210 p = 1) (hb : d52600 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6210 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6210, d52600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6210, d52600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10601 (p : Pattern) (ha : d87467 p = 1) (hb : d88558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87466 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52600 q = 1) (hb : d88553 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10600 q hb ha
    | true =>
      simp only [d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87458 q = 1) (hb : d88554 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d87458, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87458, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87459 q = 1) (hb : d88555 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d87459, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87459, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87465 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87466 q = 1) (hb : d88556 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d87466, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87466, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87466 q = 1) (hb : d88557 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87467 q = 1) (hb : d88558 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87467, d88558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87467, d88558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10602 (p : Pattern) (ha : d87481 p = 1) (hb : d88564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87468 q = 1) (hb : d88559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87468, d88559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10601 q ha hb
    | true =>
      simp only [d87468, d88559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87469 q = 1) (hb : d88560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87469, d88560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87469, d88560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87477 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87478 q = 1) (hb : d88561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87478, d88561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87478, d88561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87479 q = 1) (hb : d88562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87479, d88562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87479, d88562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87480 q = 1) (hb : d88563 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87480, d88563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87480, d88563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87481 q = 1) (hb : d88564 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87481, d88564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87481, d88564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10603 (p : Pattern) (ha : d87467 p = 1) (hb : d88568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87466 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11271 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11272 q = 1) (hb : d87458 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d87458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11272, d87458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11273 q = 1) (hb : d87459 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d87459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11273, d87459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87465 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11279 q = 1) (hb : d87466 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d87466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11279, d87466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87466 q = 1) (hb : d88567 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87467 q = 1) (hb : d88568 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87467, d88568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87467, d88568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10604 (p : Pattern) (ha : d87492 p = 1) (hb : d88574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87468 q = 1) (hb : d88569 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87468, d88569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10603 q ha hb
    | true =>
      simp only [d87468, d88569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87469 q = 1) (hb : d88570 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87469, d88570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87469, d88570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87489 q = 1) (hb : d88571 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87489, d88571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87489, d88571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87490 q = 1) (hb : d88572 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87490, d88572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87490, d88572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87491 q = 1) (hb : d88573 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87491, d88573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87491, d88573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87492 q = 1) (hb : d88574 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87492, d88574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87492, d88574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10605 (p : Pattern) (ha : d87498 p = 1) (hb : d88580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87482 q = 1) (hb : d88565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87482, d88565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10599 q ha hb
    | true =>
      simp only [d87482, d88565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10602 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87487 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87488 q = 1) (hb : d88566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87488, d88566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87488, d88566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87493 q = 1) (hb : d88575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87493, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10604 q ha hb
    | true =>
      simp only [d87493, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87494 q = 1) (hb : d88576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87494, d88576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87494, d88576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87495 q = 1) (hb : d88577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87495, d88577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87495, d88577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87496 q = 1) (hb : d88578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87496, d88578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87496, d88578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87497 q = 1) (hb : d88579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87497, d88579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87497, d88579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87498 q = 1) (hb : d88580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87498, d88580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87498, d88580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10606 (p : Pattern) (ha : d87511 p = 1) (hb : d88586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87356 q = 1) (hb : d88457 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87356, d88457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87356, d88457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10578 q ha hb
  have h2 (q : Pattern) (ha : d87357 q = 1) (hb : d88458 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87357, d88458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87357, d88458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87366 q = 1) (hb : d88466 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87366, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10578 q ha hb
    | true =>
      simp only [d87366, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10580 q ha hb
  have h4 (q : Pattern) (ha : d87367 q = 1) (hb : d88467 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87367, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87367, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87368 q = 1) (hb : d88468 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87368, d88468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87368, d88468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87429 q = 1) (hb : d88526 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87429, d88526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10589 q ha hb
    | true =>
      simp only [d87429, d88526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10595 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87441 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87442 q = 1) (hb : d88533 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87442, d88533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10596 q ha hb
    | true =>
      simp only [d87442, d88533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87443 q = 1) (hb : d88534 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87443, d88534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87443, d88534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87444 q = 1) (hb : d88535 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87444, d88535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87444, d88535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d87445 q = 1) (hb : d88536 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87445, d88536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87445, d88536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d87449 q = 1) (hb : d88540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87449, d88540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87449, d88540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10597 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d87451 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d87452 q = 1) (hb : d88541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87452, d88541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87452, d88541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d87453 q = 1) (hb : d88542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87453, d88542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d87453, d88542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d87454 q = 1) (hb : d88543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87454, d88543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87454, d88543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d87455 q = 1) (hb : d88544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87455, d88544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87455, d88544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87499 q = 1) (hb : d88581 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87499, d88581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87499, d88581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10605 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d87506 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d87507 q = 1) (hb : d88582 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87507, d88582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d87507, d88582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d87508 q = 1) (hb : d88583 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87508, d88583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d87508, d88583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d87509 q = 1) (hb : d88584 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87509, d88584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d87509, d88584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d87510 q = 1) (hb : d88585 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87510, d88585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d87510, d88585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d87511 q = 1) (hb : d88586 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87511, d88586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87511, d88586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro10607 (p : Pattern) (ha : d87517 p = 1) (hb : d88592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87512 q = 1) (hb : d88587 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87512, d88587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87512, d88587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10606 q ha hb
  have h2 (q : Pattern) (ha : d87513 q = 1) (hb : d88588 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87513, d88588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87513, d88588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87514 q = 1) (hb : d88589 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87514, d88589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87514, d88589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87515 q = 1) (hb : d88590 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87515, d88590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87515, d88590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87516 q = 1) (hb : d88591 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87516, d88591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87516, d88591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87517 q = 1) (hb : d88592 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d87517, d88592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87517, d88592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10608 (p : Pattern) (ha : d87525 p = 1) (hb : d88596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11369 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11370 q = 1) (hb : d87520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d87520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11370, d87520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11371 q = 1) (hb : d87521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d87521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11371, d87521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87523 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11373 q = 1) (hb : d87524 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d87524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11373, d87524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87524 q = 1) (hb : d88595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87525 q = 1) (hb : d88596 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87525, d88596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87525, d88596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10609 (p : Pattern) (ha : d87535 p = 1) (hb : d88602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87526 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10608 q ha hb
    | true =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87527 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87531 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87532 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87533 q = 1) (hb : d88600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87533, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87533, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87534 q = 1) (hb : d88601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87534, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87534, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87535 q = 1) (hb : d88602 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87535, d88602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87535, d88602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10610 (p : Pattern) (ha : d87545 p = 1) (hb : d88608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87540 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87540, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10609 q ha hb
    | true =>
      simp only [d87540, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87541 q = 1) (hb : d88604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87541, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87541, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87542 q = 1) (hb : d88605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87542, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87542, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87543 q = 1) (hb : d88606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87543, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87543, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87544 q = 1) (hb : d88607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87544, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87544, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87545 q = 1) (hb : d88608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87545, d88608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87545, d88608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10611 (p : Pattern) (ha : d87548 p = 1) (hb : d88611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87526 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10608 q ha hb
    | true =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87527 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87531 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87532 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87533 q = 1) (hb : d88600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87533, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87533, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87534 q = 1) (hb : d88601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87534, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87534, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87548 q = 1) (hb : d88611 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87548, d88611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87548, d88611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10612 (p : Pattern) (ha : d87555 p = 1) (hb : d88617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87540 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87540, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10609 q ha hb
    | true =>
      simp only [d87540, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87541 q = 1) (hb : d88604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87541, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87541, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87542 q = 1) (hb : d88605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87542, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87542, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87543 q = 1) (hb : d88606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87543, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87543, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87544 q = 1) (hb : d88607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87544, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87544, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87549 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87550 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87550, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10611 q ha hb
    | true =>
      simp only [d87550, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87551 q = 1) (hb : d88613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87551, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87551, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87552 q = 1) (hb : d88614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87552, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87552, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d87553 q = 1) (hb : d88615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87553, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87553, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d87554 q = 1) (hb : d88616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87554, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87554, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d87555 q = 1) (hb : d88617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87555, d88617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87555, d88617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro10613 (p : Pattern) (ha : d5009 p = 1) (hb : d52709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5009 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5009, d52709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5009, d52709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10614 (p : Pattern) (ha : d87525 p = 1) (hb : d88646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52709 q = 1) (hb : d88641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10613 q hb ha
    | true =>
      simp only [d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87520 q = 1) (hb : d88642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d87520, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87520, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87521 q = 1) (hb : d88643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d87521, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87521, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87523 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87524 q = 1) (hb : d88644 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d87524, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87524, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87524 q = 1) (hb : d88645 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87525 q = 1) (hb : d88646 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87525, d88646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87525, d88646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10615 (p : Pattern) (ha : d87535 p = 1) (hb : d88652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87526 q = 1) (hb : d88647 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87526, d88647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10614 q ha hb
    | true =>
      simp only [d87526, d88647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87527 q = 1) (hb : d88648 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87527, d88648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87527, d88648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87531 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87532 q = 1) (hb : d88649 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87532, d88649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87532, d88649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87533 q = 1) (hb : d88650 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87533, d88650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87533, d88650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87534 q = 1) (hb : d88651 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87534, d88651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87534, d88651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87535 q = 1) (hb : d88652 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87535, d88652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87535, d88652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10616 (p : Pattern) (ha : d87560 p = 1) (hb : d88622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87526 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10608 q ha hb
    | true =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87527 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87531 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87532 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87533 q = 1) (hb : d88600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87533, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87533, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87559 q = 1) (hb : d88621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87559, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87559, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87560 q = 1) (hb : d88622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87560, d88622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87560, d88622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10617 (p : Pattern) (ha : d87569 p = 1) (hb : d88629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87526 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10608 q ha hb
    | true =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87527 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87531 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87532 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87567 q = 1) (hb : d88627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87567, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87567, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87568 q = 1) (hb : d88628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87568, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87568, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87569 q = 1) (hb : d88629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87569, d88629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87569, d88629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10618 (p : Pattern) (ha : d87579 p = 1) (hb : d88634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87578 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52707 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11366 q = 1) (hb : d52707 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11367 q = 1) (hb : d87576 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d87576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11367, d87576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11368 q = 1) (hb : d87577 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d87577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11368, d87577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11369 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11370 q = 1) (hb : d87520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d87520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11370, d87520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11371 q = 1) (hb : d87521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d87521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11371, d87521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11372 q = 1) (hb : d87578 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d87578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11372, d87578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87578 q = 1) (hb : d88633 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87579 q = 1) (hb : d88634 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87579, d88634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87579, d88634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10619 (p : Pattern) (ha : d87585 p = 1) (hb : d88640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87580 q = 1) (hb : d88635 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87580, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10618 q ha hb
    | true =>
      simp only [d87580, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87581 q = 1) (hb : d88636 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87581, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87581, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87527 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87582 q = 1) (hb : d88637 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87582, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87582, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87583 q = 1) (hb : d88638 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87583, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87583, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87584 q = 1) (hb : d88639 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87584, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87584, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87585 q = 1) (hb : d88640 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87585, d88640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87585, d88640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10620 (p : Pattern) (ha : d87591 p = 1) (hb : d88602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87526 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10608 q ha hb
    | true =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87527 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87588 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87588, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87588, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87589 q = 1) (hb : d88600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87589, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87589, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87590 q = 1) (hb : d88601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87590, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87590, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87591 q = 1) (hb : d88602 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87591, d88602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87591, d88602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10621 (p : Pattern) (ha : d87597 p = 1) (hb : d88659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87562 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87563 q = 1) (hb : d88623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87563, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10616 q ha hb
    | true =>
      simp only [d87563, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87564 q = 1) (hb : d88624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87564, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87564, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87565 q = 1) (hb : d88625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87565, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87565, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87566 q = 1) (hb : d88626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87566, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87566, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87572 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87573 q = 1) (hb : d88630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87573, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10617 q ha hb
    | true =>
      simp only [d87573, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87574 q = 1) (hb : d88631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87574, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87574, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87575 q = 1) (hb : d88632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87575, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87575, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87586 q = 1) (hb : d88653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87586, d88653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10619 q ha hb
    | true =>
      simp only [d87586, d88653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10615 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87540 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d87587 q = 1) (hb : d88654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87587, d88654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87587, d88654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d87592 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87592, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10620 q ha hb
    | true =>
      simp only [d87592, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87593 q = 1) (hb : d88655 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87593, d88655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87593, d88655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87594 q = 1) (hb : d88656 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87594, d88656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87594, d88656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87595 q = 1) (hb : d88657 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87595, d88657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87595, d88657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d87596 q = 1) (hb : d88658 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87596, d88658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87596, d88658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87597 q = 1) (hb : d88659 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87597, d88659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87597, d88659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10622 (p : Pattern) (ha : d87548 p = 1) (hb : d88670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87526 q = 1) (hb : d88647 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87526, d88647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10614 q ha hb
    | true =>
      simp only [d87526, d88647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87527 q = 1) (hb : d88648 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87527, d88648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87527, d88648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87531 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87532 q = 1) (hb : d88649 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87532, d88649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87532, d88649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87533 q = 1) (hb : d88650 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87533, d88650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87533, d88650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87534 q = 1) (hb : d88651 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87534, d88651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87534, d88651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87548 q = 1) (hb : d88670 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87548, d88670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87548, d88670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10623 (p : Pattern) (ha : d87598 p = 1) (hb : d88660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87526 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10608 q ha hb
    | true =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87527 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87531 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87532 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87533 q = 1) (hb : d88600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87533, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87533, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87559 q = 1) (hb : d88621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87559, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87559, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87598 q = 1) (hb : d88660 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87598, d88660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87598, d88660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10624 (p : Pattern) (ha : d87604 p = 1) (hb : d88665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87526 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10608 q ha hb
    | true =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87527 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87531 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87532 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87532, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87567 q = 1) (hb : d88627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87567, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87567, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87568 q = 1) (hb : d88628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87568, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87568, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87604 q = 1) (hb : d88665 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87604, d88665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87604, d88665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10625 (p : Pattern) (ha : d87609 p = 1) (hb : d88669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87580 q = 1) (hb : d88635 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87580, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10618 q ha hb
    | true =>
      simp only [d87580, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87581 q = 1) (hb : d88636 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87581, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87581, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87527 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87582 q = 1) (hb : d88637 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87582, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87582, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87583 q = 1) (hb : d88638 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87583, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87583, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87584 q = 1) (hb : d88639 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87584, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87584, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87609 q = 1) (hb : d88669 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87609, d88669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87609, d88669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10626 (p : Pattern) (ha : d87612 p = 1) (hb : d88611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87526 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10608 q ha hb
    | true =>
      simp only [d87526, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87527 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87527, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87588 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87588, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87588, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87589 q = 1) (hb : d88600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87589, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87589, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87590 q = 1) (hb : d88601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87590, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87590, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87612 q = 1) (hb : d88611 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87612, d88611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87612, d88611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10627 (p : Pattern) (ha : d87618 p = 1) (hb : d88677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87562 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87563 q = 1) (hb : d88623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87563, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10616 q ha hb
    | true =>
      simp only [d87563, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87564 q = 1) (hb : d88624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87564, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87564, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87565 q = 1) (hb : d88625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87565, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87565, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87566 q = 1) (hb : d88626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87566, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87566, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87572 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87573 q = 1) (hb : d88630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87573, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10617 q ha hb
    | true =>
      simp only [d87573, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87574 q = 1) (hb : d88631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87574, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87574, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87575 q = 1) (hb : d88632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87575, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87575, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87586 q = 1) (hb : d88653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87586, d88653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10619 q ha hb
    | true =>
      simp only [d87586, d88653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10615 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87540 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d87587 q = 1) (hb : d88654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87587, d88654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87587, d88654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d87592 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87592, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10620 q ha hb
    | true =>
      simp only [d87592, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87593 q = 1) (hb : d88655 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87593, d88655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87593, d88655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87594 q = 1) (hb : d88656 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87594, d88656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87594, d88656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87595 q = 1) (hb : d88657 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87595, d88657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87595, d88657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d87596 q = 1) (hb : d88658 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87596, d88658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87596, d88658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d87599 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d87600 q = 1) (hb : d88661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87600, d88661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10623 q ha hb
    | true =>
      simp only [d87600, d88661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d87601 q = 1) (hb : d88662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87601, d88662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87601, d88662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d87602 q = 1) (hb : d88663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87602, d88663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d87602, d88663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d87603 q = 1) (hb : d88664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87603, d88664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87603, d88664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d87605 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d87606 q = 1) (hb : d88666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87606, d88666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10624 q ha hb
    | true =>
      simp only [d87606, d88666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d87607 q = 1) (hb : d88667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87607, d88667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87607, d88667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d87608 q = 1) (hb : d88668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87608, d88668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d87608, d88668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d87610 q = 1) (hb : d88671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87610, d88671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10625 q ha hb
    | true =>
      simp only [d87610, d88671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10622 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d87550 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d87611 q = 1) (hb : d88672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87611, d88672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d87611, d88672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d87613 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87613, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10626 q ha hb
    | true =>
      simp only [d87613, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d87614 q = 1) (hb : d88673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87614, d88673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d87614, d88673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d87615 q = 1) (hb : d88674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87615, d88674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d87615, d88674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d87616 q = 1) (hb : d88675 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87616, d88675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d87616, d88675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d87617 q = 1) (hb : d88676 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87617, d88676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d87617, d88676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d87618 q = 1) (hb : d88677 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87618, d88677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87618, d88677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro10628 (p : Pattern) (ha : d87625 p = 1) (hb : d88684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87540 q = 1) (hb : d88679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87540, d88679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10615 q ha hb
    | true =>
      simp only [d87540, d88679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87541 q = 1) (hb : d88680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87541, d88680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87541, d88680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87542 q = 1) (hb : d88681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87542, d88681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87542, d88681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87543 q = 1) (hb : d88682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87543, d88682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87543, d88682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87544 q = 1) (hb : d88683 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87544, d88683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87544, d88683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87624 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87625 q = 1) (hb : d88684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87625, d88684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87625, d88684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10629 (p : Pattern) (ha : d87638 p = 1) (hb : d88691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87610 q = 1) (hb : d88671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87610, d88671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10625 q ha hb
    | true =>
      simp only [d87610, d88671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10622 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87550 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87611 q = 1) (hb : d88672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87611, d88672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87611, d88672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87613 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87613, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10626 q ha hb
    | true =>
      simp only [d87613, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87614 q = 1) (hb : d88673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87614, d88673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87614, d88673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87615 q = 1) (hb : d88674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87615, d88674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87615, d88674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87636 q = 1) (hb : d88689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87636, d88689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87636, d88689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87637 q = 1) (hb : d88690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87637, d88690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87637, d88690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87638 q = 1) (hb : d88691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87638, d88691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87638, d88691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10630 (p : Pattern) (ha : d87651 p = 1) (hb : d88698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52884 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11537 q = 1) (hb : d52884 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11538 q = 1) (hb : d87646 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d87646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11538, d87646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11539 q = 1) (hb : d87647 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d87647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11539, d87647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11541 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11542 q = 1) (hb : d87648 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d87648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11542, d87648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11543 q = 1) (hb : d87649 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d87649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11543, d87649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11544 q = 1) (hb : d87650 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d87650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11544, d87650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87650 q = 1) (hb : d88697 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87651 q = 1) (hb : d88698 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87651, d88698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87651, d88698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10631 (p : Pattern) (ha : d87663 p = 1) (hb : d88704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87652 q = 1) (hb : d88699 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87652, d88699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10630 q ha hb
    | true =>
      simp only [d87652, d88699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87653 q = 1) (hb : d88700 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87653, d88700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87653, d88700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87659 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87660 q = 1) (hb : d88701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87660, d88701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87660, d88701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87661 q = 1) (hb : d88702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87661, d88702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87661, d88702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87662 q = 1) (hb : d88703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87662, d88703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87662, d88703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87663 q = 1) (hb : d88704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87663, d88704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87663, d88704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10632 (p : Pattern) (ha : d6349 p = 1) (hb : d52889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6349 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6349, d52889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6349, d52889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10633 (p : Pattern) (ha : d87657 p = 1) (hb : d88710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87656 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52889 q = 1) (hb : d88705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10632 q hb ha
    | true =>
      simp only [d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87648 q = 1) (hb : d88706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d87648, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87648, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87649 q = 1) (hb : d88707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d87649, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87649, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87655 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87656 q = 1) (hb : d88708 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d87656, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87656, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87656 q = 1) (hb : d88709 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87657 q = 1) (hb : d88710 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87657, d88710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87657, d88710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10634 (p : Pattern) (ha : d87671 p = 1) (hb : d88716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87658 q = 1) (hb : d88711 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87658, d88711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10633 q ha hb
    | true =>
      simp only [d87658, d88711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87659 q = 1) (hb : d88712 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87659, d88712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87659, d88712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87667 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87668 q = 1) (hb : d88713 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87668, d88713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87668, d88713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87669 q = 1) (hb : d88714 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87669, d88714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87669, d88714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87670 q = 1) (hb : d88715 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87670, d88715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87670, d88715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87671 q = 1) (hb : d88716 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87671, d88716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87671, d88716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10635 (p : Pattern) (ha : d87657 p = 1) (hb : d88720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87656 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11541 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11542 q = 1) (hb : d87648 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d87648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11542, d87648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11543 q = 1) (hb : d87649 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d87649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11543, d87649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87655 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11549 q = 1) (hb : d87656 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d87656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11549, d87656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87656 q = 1) (hb : d88719 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87657 q = 1) (hb : d88720 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87657, d88720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87657, d88720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10636 (p : Pattern) (ha : d87682 p = 1) (hb : d88726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87658 q = 1) (hb : d88721 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87658, d88721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10635 q ha hb
    | true =>
      simp only [d87658, d88721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87659 q = 1) (hb : d88722 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87659, d88722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87659, d88722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87679 q = 1) (hb : d88723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87679, d88723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87679, d88723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87680 q = 1) (hb : d88724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87680, d88724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87680, d88724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87681 q = 1) (hb : d88725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87681, d88725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87681, d88725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87682 q = 1) (hb : d88726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87682, d88726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87682, d88726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10637 (p : Pattern) (ha : d87688 p = 1) (hb : d88732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87672 q = 1) (hb : d88717 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87672, d88717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10631 q ha hb
    | true =>
      simp only [d87672, d88717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10634 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87677 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87678 q = 1) (hb : d88718 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87678, d88718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87678, d88718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87683 q = 1) (hb : d88727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87683, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10636 q ha hb
    | true =>
      simp only [d87683, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87684 q = 1) (hb : d88728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87684, d88728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87684, d88728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87685 q = 1) (hb : d88729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87685, d88729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87685, d88729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87686 q = 1) (hb : d88730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87686, d88730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87686, d88730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87687 q = 1) (hb : d88731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87687, d88731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87687, d88731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87688 q = 1) (hb : d88732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87688, d88732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87688, d88732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10638 (p : Pattern) (ha : d87701 p = 1) (hb : d88738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87546 q = 1) (hb : d88609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87546, d88609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87546, d88609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10610 q ha hb
  have h2 (q : Pattern) (ha : d87547 q = 1) (hb : d88610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87547, d88610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87547, d88610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87556 q = 1) (hb : d88618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87556, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10610 q ha hb
    | true =>
      simp only [d87556, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10612 q ha hb
  have h4 (q : Pattern) (ha : d87557 q = 1) (hb : d88619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87557, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87557, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87558 q = 1) (hb : d88620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87558, d88620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87558, d88620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87619 q = 1) (hb : d88678 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87619, d88678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10621 q ha hb
    | true =>
      simp only [d87619, d88678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10627 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87631 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87632 q = 1) (hb : d88685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87632, d88685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10628 q ha hb
    | true =>
      simp only [d87632, d88685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87633 q = 1) (hb : d88686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87633, d88686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87633, d88686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87634 q = 1) (hb : d88687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87634, d88687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87634, d88687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d87635 q = 1) (hb : d88688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87635, d88688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87635, d88688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d87639 q = 1) (hb : d88692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87639, d88692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87639, d88692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10629 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d87641 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d87642 q = 1) (hb : d88693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87642, d88693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87642, d88693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d87643 q = 1) (hb : d88694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87643, d88694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d87643, d88694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d87644 q = 1) (hb : d88695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87644, d88695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87644, d88695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d87645 q = 1) (hb : d88696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87645, d88696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87645, d88696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87689 q = 1) (hb : d88733 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87689, d88733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87689, d88733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10637 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d87696 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d87697 q = 1) (hb : d88734 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87697, d88734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d87697, d88734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d87698 q = 1) (hb : d88735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87698, d88735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d87698, d88735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d87699 q = 1) (hb : d88736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87699, d88736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d87699, d88736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d87700 q = 1) (hb : d88737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87700, d88737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d87700, d88737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d87701 q = 1) (hb : d88738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87701, d88738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87701, d88738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro10639 (p : Pattern) (ha : d87707 p = 1) (hb : d88744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87702 q = 1) (hb : d88739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87702, d88739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87702, d88739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10638 q ha hb
  have h2 (q : Pattern) (ha : d87703 q = 1) (hb : d88740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87703, d88740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87703, d88740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87704 q = 1) (hb : d88741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87704, d88741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87704, d88741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87705 q = 1) (hb : d88742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87705, d88742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87705, d88742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87706 q = 1) (hb : d88743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87706, d88743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87706, d88743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87707 q = 1) (hb : d88744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d87707, d88744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87707, d88744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10640 (p : Pattern) (ha : d87716 p = 1) (hb : d88749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87715 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11640 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11641 q = 1) (hb : d87711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d87711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11641, d87711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11642 q = 1) (hb : d87712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d87712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11642, d87712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87714 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11644 q = 1) (hb : d87715 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d87715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11644, d87715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87715 q = 1) (hb : d88748 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87716 q = 1) (hb : d88749 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87716, d88749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87716, d88749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10641 (p : Pattern) (ha : d87726 p = 1) (hb : d88755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87717 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10640 q ha hb
    | true =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87718 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87722 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87723 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87724 q = 1) (hb : d88753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87724, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87724, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87725 q = 1) (hb : d88754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87725, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87725, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87726 q = 1) (hb : d88755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87726, d88755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87726, d88755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10642 (p : Pattern) (ha : d87736 p = 1) (hb : d88761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87731 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87731, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10641 q ha hb
    | true =>
      simp only [d87731, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87732 q = 1) (hb : d88757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87732, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87732, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87733 q = 1) (hb : d88758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87733, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87733, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87734 q = 1) (hb : d88759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87734, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87734, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87735 q = 1) (hb : d88760 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87735, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87735, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87736 q = 1) (hb : d88761 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87736, d88761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87736, d88761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10643 (p : Pattern) (ha : d87739 p = 1) (hb : d88764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87717 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10640 q ha hb
    | true =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87718 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87722 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87723 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87724 q = 1) (hb : d88753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87724, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87724, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87725 q = 1) (hb : d88754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87725, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87725, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87739 q = 1) (hb : d88764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87739, d88764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87739, d88764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10644 (p : Pattern) (ha : d87746 p = 1) (hb : d88770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87731 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87731, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10641 q ha hb
    | true =>
      simp only [d87731, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87732 q = 1) (hb : d88757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87732, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87732, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87733 q = 1) (hb : d88758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87733, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87733, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87734 q = 1) (hb : d88759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87734, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87734, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87735 q = 1) (hb : d88760 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87735, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87735, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87740 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87741 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87741, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10643 q ha hb
    | true =>
      simp only [d87741, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87742 q = 1) (hb : d88766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87742, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87742, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87743 q = 1) (hb : d88767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87743, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87743, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d87744 q = 1) (hb : d88768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87744, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87744, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d87745 q = 1) (hb : d88769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87745, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87745, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d87746 q = 1) (hb : d88770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87746, d88770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87746, d88770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro10645 (p : Pattern) (ha : d5120 p = 1) (hb : d53030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1584 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1585 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1586 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1586, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5120 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5120, d53030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5120, d53030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10646 (p : Pattern) (ha : d87716 p = 1) (hb : d88799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87715 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53030 q = 1) (hb : d88794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10645 q hb ha
    | true =>
      simp only [d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87711 q = 1) (hb : d88795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d87711, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87711, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87712 q = 1) (hb : d88796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d87712, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87712, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87714 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87715 q = 1) (hb : d88797 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d87715, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87715, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87715 q = 1) (hb : d88798 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87716 q = 1) (hb : d88799 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87716, d88799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87716, d88799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10647 (p : Pattern) (ha : d87726 p = 1) (hb : d88805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87717 q = 1) (hb : d88800 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87717, d88800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10646 q ha hb
    | true =>
      simp only [d87717, d88800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87718 q = 1) (hb : d88801 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87718, d88801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87718, d88801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87722 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87723 q = 1) (hb : d88802 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87723, d88802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87723, d88802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87724 q = 1) (hb : d88803 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87724, d88803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87724, d88803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87725 q = 1) (hb : d88804 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87725, d88804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87725, d88804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87726 q = 1) (hb : d88805 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87726, d88805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87726, d88805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10648 (p : Pattern) (ha : d87751 p = 1) (hb : d88775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87717 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10640 q ha hb
    | true =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87718 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87722 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87723 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87724 q = 1) (hb : d88753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87724, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87724, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87750 q = 1) (hb : d88774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87750, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87750, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87751 q = 1) (hb : d88775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87751, d88775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87751, d88775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10649 (p : Pattern) (ha : d87760 p = 1) (hb : d88782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87717 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10640 q ha hb
    | true =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87718 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87722 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87723 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87758 q = 1) (hb : d88780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87758, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87758, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87759 q = 1) (hb : d88781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87759, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87759, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87760 q = 1) (hb : d88782 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87760, d88782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87760, d88782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10650 (p : Pattern) (ha : d87770 p = 1) (hb : d88787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53028 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11637 q = 1) (hb : d53028 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11638 q = 1) (hb : d87767 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d87767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11638, d87767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11639 q = 1) (hb : d87768 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d87768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11639, d87768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11640 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11641 q = 1) (hb : d87711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d87711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11641, d87711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11642 q = 1) (hb : d87712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d87712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11642, d87712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11643 q = 1) (hb : d87769 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d87769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11643, d87769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87769 q = 1) (hb : d88786 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87770 q = 1) (hb : d88787 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87770, d88787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87770, d88787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10651 (p : Pattern) (ha : d87776 p = 1) (hb : d88793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87771 q = 1) (hb : d88788 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87771, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10650 q ha hb
    | true =>
      simp only [d87771, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87772 q = 1) (hb : d88789 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87772, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87772, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87718 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87773 q = 1) (hb : d88790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87773, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87773, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87774 q = 1) (hb : d88791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87774, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87774, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87775 q = 1) (hb : d88792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87775, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87775, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87776 q = 1) (hb : d88793 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87776, d88793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87776, d88793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10652 (p : Pattern) (ha : d87782 p = 1) (hb : d88755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87717 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10640 q ha hb
    | true =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87718 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87779 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87779, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87779, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87780 q = 1) (hb : d88753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87780, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87780, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87781 q = 1) (hb : d88754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87781, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87781, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87782 q = 1) (hb : d88755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87782, d88755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87782, d88755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10653 (p : Pattern) (ha : d87788 p = 1) (hb : d88812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87754 q = 1) (hb : d88776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87754, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10648 q ha hb
    | true =>
      simp only [d87754, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87755 q = 1) (hb : d88777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87755, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87755, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87756 q = 1) (hb : d88778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87756, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87756, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87757 q = 1) (hb : d88779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87757, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87757, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87763 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87764 q = 1) (hb : d88783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87764, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10649 q ha hb
    | true =>
      simp only [d87764, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87765 q = 1) (hb : d88784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87765, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87765, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87766 q = 1) (hb : d88785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87766, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87766, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87777 q = 1) (hb : d88806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87777, d88806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10651 q ha hb
    | true =>
      simp only [d87777, d88806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10647 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87731 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d87778 q = 1) (hb : d88807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87778, d88807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87778, d88807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d87783 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87783, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10652 q ha hb
    | true =>
      simp only [d87783, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87784 q = 1) (hb : d88808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87784, d88808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87784, d88808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87785 q = 1) (hb : d88809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87785, d88809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87785, d88809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87786 q = 1) (hb : d88810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87786, d88810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87786, d88810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d87787 q = 1) (hb : d88811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87787, d88811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87787, d88811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87788 q = 1) (hb : d88812 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87788, d88812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87788, d88812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10654 (p : Pattern) (ha : d87739 p = 1) (hb : d88823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87717 q = 1) (hb : d88800 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87717, d88800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10646 q ha hb
    | true =>
      simp only [d87717, d88800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87718 q = 1) (hb : d88801 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87718, d88801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87718, d88801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87722 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87723 q = 1) (hb : d88802 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87723, d88802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87723, d88802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87724 q = 1) (hb : d88803 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87724, d88803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87724, d88803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87725 q = 1) (hb : d88804 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87725, d88804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87725, d88804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87739 q = 1) (hb : d88823 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87739, d88823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87739, d88823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10655 (p : Pattern) (ha : d87789 p = 1) (hb : d88813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87717 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10640 q ha hb
    | true =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87718 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87722 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87723 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87724 q = 1) (hb : d88753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87724, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87724, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87750 q = 1) (hb : d88774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87750, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87750, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87789 q = 1) (hb : d88813 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87789, d88813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87789, d88813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10656 (p : Pattern) (ha : d87795 p = 1) (hb : d88818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87717 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10640 q ha hb
    | true =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87718 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87722 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87723 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87723, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87758 q = 1) (hb : d88780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87758, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87758, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87759 q = 1) (hb : d88781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87759, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87759, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87795 q = 1) (hb : d88818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87795, d88818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87795, d88818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10657 (p : Pattern) (ha : d87800 p = 1) (hb : d88822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87771 q = 1) (hb : d88788 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87771, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10650 q ha hb
    | true =>
      simp only [d87771, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87772 q = 1) (hb : d88789 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87772, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87772, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87718 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87773 q = 1) (hb : d88790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87773, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87773, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87774 q = 1) (hb : d88791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87774, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87774, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87775 q = 1) (hb : d88792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87775, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87775, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87800 q = 1) (hb : d88822 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87800, d88822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87800, d88822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10658 (p : Pattern) (ha : d87803 p = 1) (hb : d88764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87717 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10640 q ha hb
    | true =>
      simp only [d87717, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87718 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87718, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87779 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87779, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87779, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87780 q = 1) (hb : d88753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87780, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87780, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87781 q = 1) (hb : d88754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87781, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87781, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87803 q = 1) (hb : d88764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87803, d88764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87803, d88764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10659 (p : Pattern) (ha : d87809 p = 1) (hb : d88830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87754 q = 1) (hb : d88776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87754, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10648 q ha hb
    | true =>
      simp only [d87754, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87755 q = 1) (hb : d88777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87755, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87755, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87756 q = 1) (hb : d88778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87756, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87756, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87757 q = 1) (hb : d88779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87757, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87757, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87763 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87764 q = 1) (hb : d88783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87764, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10649 q ha hb
    | true =>
      simp only [d87764, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87765 q = 1) (hb : d88784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87765, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87765, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87766 q = 1) (hb : d88785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87766, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87766, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87777 q = 1) (hb : d88806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87777, d88806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10651 q ha hb
    | true =>
      simp only [d87777, d88806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10647 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87731 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d87778 q = 1) (hb : d88807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87778, d88807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87778, d88807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d87783 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87783, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10652 q ha hb
    | true =>
      simp only [d87783, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87784 q = 1) (hb : d88808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87784, d88808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87784, d88808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87785 q = 1) (hb : d88809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87785, d88809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87785, d88809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87786 q = 1) (hb : d88810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87786, d88810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87786, d88810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d87787 q = 1) (hb : d88811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87787, d88811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87787, d88811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d87790 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d87791 q = 1) (hb : d88814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87791, d88814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10655 q ha hb
    | true =>
      simp only [d87791, d88814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d87792 q = 1) (hb : d88815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87792, d88815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87792, d88815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d87793 q = 1) (hb : d88816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87793, d88816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d87793, d88816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d87794 q = 1) (hb : d88817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87794, d88817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87794, d88817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d87796 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d87797 q = 1) (hb : d88819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87797, d88819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10656 q ha hb
    | true =>
      simp only [d87797, d88819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d87798 q = 1) (hb : d88820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87798, d88820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87798, d88820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d87799 q = 1) (hb : d88821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87799, d88821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d87799, d88821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d87801 q = 1) (hb : d88824 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87801, d88824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10657 q ha hb
    | true =>
      simp only [d87801, d88824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10654 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d87741 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d87802 q = 1) (hb : d88825 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87802, d88825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d87802, d88825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d87804 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87804, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10658 q ha hb
    | true =>
      simp only [d87804, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d87805 q = 1) (hb : d88826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87805, d88826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d87805, d88826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d87806 q = 1) (hb : d88827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87806, d88827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d87806, d88827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d87807 q = 1) (hb : d88828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87807, d88828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d87807, d88828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d87808 q = 1) (hb : d88829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87808, d88829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d87808, d88829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d87809 q = 1) (hb : d88830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87809, d88830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87809, d88830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro10660 (p : Pattern) (ha : d87816 p = 1) (hb : d88837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87731 q = 1) (hb : d88832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87731, d88832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10647 q ha hb
    | true =>
      simp only [d87731, d88832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87732 q = 1) (hb : d88833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87732, d88833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87732, d88833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87733 q = 1) (hb : d88834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87733, d88834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87733, d88834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87734 q = 1) (hb : d88835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87734, d88835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87734, d88835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87735 q = 1) (hb : d88836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87735, d88836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87735, d88836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87815 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87816 q = 1) (hb : d88837 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87816, d88837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87816, d88837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10661 (p : Pattern) (ha : d87829 p = 1) (hb : d88844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87801 q = 1) (hb : d88824 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87801, d88824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10657 q ha hb
    | true =>
      simp only [d87801, d88824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10654 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87802 q = 1) (hb : d88825 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87802, d88825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87802, d88825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87804 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87804, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10658 q ha hb
    | true =>
      simp only [d87804, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87805 q = 1) (hb : d88826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87805, d88826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87805, d88826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87806 q = 1) (hb : d88827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87806, d88827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87806, d88827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87827 q = 1) (hb : d88842 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87827, d88842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87827, d88842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87828 q = 1) (hb : d88843 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87828, d88843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87828, d88843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87829 q = 1) (hb : d88844 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87829, d88844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87829, d88844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10662 (p : Pattern) (ha : d87842 p = 1) (hb : d88851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87841 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53199 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11808 q = 1) (hb : d53199 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11809 q = 1) (hb : d87837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d87837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11809, d87837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11810 q = 1) (hb : d87838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d87838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11810, d87838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11812 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11813 q = 1) (hb : d87839 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d87839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11813, d87839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11814 q = 1) (hb : d87840 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d87840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11814, d87840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11815 q = 1) (hb : d87841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d87841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11815, d87841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87841 q = 1) (hb : d88850 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87842 q = 1) (hb : d88851 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87842, d88851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87842, d88851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10663 (p : Pattern) (ha : d87854 p = 1) (hb : d88857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87843 q = 1) (hb : d88852 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87843, d88852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10662 q ha hb
    | true =>
      simp only [d87843, d88852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87844 q = 1) (hb : d88853 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87844, d88853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87844, d88853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87850 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87851 q = 1) (hb : d88854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87851, d88854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87851, d88854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87852 q = 1) (hb : d88855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87852, d88855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87852, d88855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87853 q = 1) (hb : d88856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87853, d88856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87853, d88856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87854 q = 1) (hb : d88857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87854, d88857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87854, d88857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10664 (p : Pattern) (ha : d6495 p = 1) (hb : d53204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h8 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1869 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1870 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1871 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1872 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1872, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6495 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6495, d53204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6495, d53204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10665 (p : Pattern) (ha : d87848 p = 1) (hb : d88863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87847 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53204 q = 1) (hb : d88858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10664 q hb ha
    | true =>
      simp only [d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87839 q = 1) (hb : d88859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d87839, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87839, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87840 q = 1) (hb : d88860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d87840, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87840, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87846 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87847 q = 1) (hb : d88861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d87847, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87847, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87847 q = 1) (hb : d88862 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87848 q = 1) (hb : d88863 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87848, d88863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87848, d88863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10666 (p : Pattern) (ha : d87862 p = 1) (hb : d88869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87849 q = 1) (hb : d88864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87849, d88864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10665 q ha hb
    | true =>
      simp only [d87849, d88864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87850 q = 1) (hb : d88865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87850, d88865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87850, d88865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87858 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87859 q = 1) (hb : d88866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87859, d88866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87859, d88866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87860 q = 1) (hb : d88867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87860, d88867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87860, d88867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87861 q = 1) (hb : d88868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87861, d88868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87861, d88868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87862 q = 1) (hb : d88869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87862, d88869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87862, d88869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10667 (p : Pattern) (ha : d87848 p = 1) (hb : d88873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87847 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11812 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11813 q = 1) (hb : d87839 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d87839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11813, d87839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11814 q = 1) (hb : d87840 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d87840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11814, d87840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87846 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11820 q = 1) (hb : d87847 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d87847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11820, d87847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87847 q = 1) (hb : d88872 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87848 q = 1) (hb : d88873 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87848, d88873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87848, d88873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10668 (p : Pattern) (ha : d87873 p = 1) (hb : d88879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87849 q = 1) (hb : d88874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87849, d88874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10667 q ha hb
    | true =>
      simp only [d87849, d88874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87850 q = 1) (hb : d88875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87850, d88875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87850, d88875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87870 q = 1) (hb : d88876 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87870, d88876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87870, d88876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87871 q = 1) (hb : d88877 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87871, d88877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87871, d88877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87872 q = 1) (hb : d88878 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87872, d88878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87872, d88878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87873 q = 1) (hb : d88879 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87873, d88879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87873, d88879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10669 (p : Pattern) (ha : d87879 p = 1) (hb : d88885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87863 q = 1) (hb : d88870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87863, d88870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10663 q ha hb
    | true =>
      simp only [d87863, d88870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10666 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87868 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87869 q = 1) (hb : d88871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87869, d88871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87869, d88871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87874 q = 1) (hb : d88880 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87874, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10668 q ha hb
    | true =>
      simp only [d87874, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87875 q = 1) (hb : d88881 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87875, d88881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87875, d88881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87876 q = 1) (hb : d88882 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87876, d88882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87876, d88882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87877 q = 1) (hb : d88883 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87877, d88883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87877, d88883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87878 q = 1) (hb : d88884 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87878, d88884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87878, d88884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87879 q = 1) (hb : d88885 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87879, d88885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87879, d88885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10670 (p : Pattern) (ha : d87892 p = 1) (hb : d88891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87737 q = 1) (hb : d88762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87737, d88762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87737, d88762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10642 q ha hb
  have h2 (q : Pattern) (ha : d87738 q = 1) (hb : d88763 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87738, d88763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87738, d88763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87747 q = 1) (hb : d88771 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87747, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10642 q ha hb
    | true =>
      simp only [d87747, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10644 q ha hb
  have h4 (q : Pattern) (ha : d87748 q = 1) (hb : d88772 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87748, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87748, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87749 q = 1) (hb : d88773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87749, d88773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87749, d88773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87810 q = 1) (hb : d88831 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87810, d88831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10653 q ha hb
    | true =>
      simp only [d87810, d88831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10659 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87822 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87823 q = 1) (hb : d88838 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87823, d88838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10660 q ha hb
    | true =>
      simp only [d87823, d88838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87824 q = 1) (hb : d88839 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87824, d88839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87824, d88839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87825 q = 1) (hb : d88840 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87825, d88840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87825, d88840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d87826 q = 1) (hb : d88841 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87826, d88841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87826, d88841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d87830 q = 1) (hb : d88845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87830, d88845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87830, d88845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10661 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d87832 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d87833 q = 1) (hb : d88846 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87833, d88846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87833, d88846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d87834 q = 1) (hb : d88847 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87834, d88847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d87834, d88847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d87835 q = 1) (hb : d88848 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87835, d88848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87835, d88848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d87836 q = 1) (hb : d88849 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87836, d88849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87836, d88849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87880 q = 1) (hb : d88886 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87880, d88886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87880, d88886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10669 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d87887 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d87888 q = 1) (hb : d88887 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87888, d88887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d87888, d88887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d87889 q = 1) (hb : d88888 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87889, d88888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d87889, d88888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d87890 q = 1) (hb : d88889 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87890, d88889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d87890, d88889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d87891 q = 1) (hb : d88890 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87891, d88890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d87891, d88890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d87892 q = 1) (hb : d88891 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87892, d88891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87892, d88891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro10671 (p : Pattern) (ha : d87898 p = 1) (hb : d88897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87893 q = 1) (hb : d88892 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87893, d88892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87893, d88892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10670 q ha hb
  have h2 (q : Pattern) (ha : d87894 q = 1) (hb : d88893 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87894, d88893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87894, d88893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87895 q = 1) (hb : d88894 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87895, d88894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87895, d88894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87896 q = 1) (hb : d88895 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87896, d88895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87896, d88895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87897 q = 1) (hb : d88896 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87897, d88896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87897, d88896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87898 q = 1) (hb : d88897 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d87898, d88897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87898, d88897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10672 (p : Pattern) (ha : d87908 p = 1) (hb : d88903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87907 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11912 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11913 q = 1) (hb : d87903 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d87903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11913, d87903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11914 q = 1) (hb : d87904 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d87904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11914, d87904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87906 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11916 q = 1) (hb : d87907 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d87907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11916, d87907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87907 q = 1) (hb : d88902 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87908 q = 1) (hb : d88903 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87908, d88903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87908, d88903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10673 (p : Pattern) (ha : d87918 p = 1) (hb : d88909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87909 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10672 q ha hb
    | true =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87910 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87914 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87915 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87916 q = 1) (hb : d88907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87916, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87916, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87917 q = 1) (hb : d88908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87917, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87917, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87918 q = 1) (hb : d88909 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87918, d88909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87918, d88909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10674 (p : Pattern) (ha : d87928 p = 1) (hb : d88915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87923 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87923, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10673 q ha hb
    | true =>
      simp only [d87923, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87924 q = 1) (hb : d88911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87924, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87924, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87925 q = 1) (hb : d88912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87925, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87925, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87926 q = 1) (hb : d88913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87926, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87926, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87927 q = 1) (hb : d88914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87927, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87927, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87928 q = 1) (hb : d88915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87928, d88915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87928, d88915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10675 (p : Pattern) (ha : d87931 p = 1) (hb : d88918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87909 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10672 q ha hb
    | true =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87910 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87914 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87915 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87916 q = 1) (hb : d88907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87916, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87916, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87917 q = 1) (hb : d88908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87917, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87917, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87931 q = 1) (hb : d88918 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87931, d88918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87931, d88918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10676 (p : Pattern) (ha : d87938 p = 1) (hb : d88924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87923 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87923, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10673 q ha hb
    | true =>
      simp only [d87923, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87924 q = 1) (hb : d88911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87924, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87924, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87925 q = 1) (hb : d88912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87925, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87925, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87926 q = 1) (hb : d88913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87926, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87926, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87927 q = 1) (hb : d88914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87927, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87927, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87932 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87933 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87933, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10675 q ha hb
    | true =>
      simp only [d87933, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87934 q = 1) (hb : d88920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87934, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87934, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87935 q = 1) (hb : d88921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87935, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87935, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d87936 q = 1) (hb : d88922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87936, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87936, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d87937 q = 1) (hb : d88923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87937, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87937, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d87938 q = 1) (hb : d88924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87938, d88924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87938, d88924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro10677 (p : Pattern) (ha : d5237 p = 1) (hb : d53351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2055 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2056 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2067 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2068 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2069 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2069, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5237 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5237, d53351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5237, d53351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10678 (p : Pattern) (ha : d87908 p = 1) (hb : d88953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87907 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53351 q = 1) (hb : d88948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10677 q hb ha
    | true =>
      simp only [d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87903 q = 1) (hb : d88949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d87903, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87903, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87904 q = 1) (hb : d88950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d87904, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87904, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87906 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87907 q = 1) (hb : d88951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d87907, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87907, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87907 q = 1) (hb : d88952 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87908 q = 1) (hb : d88953 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87908, d88953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87908, d88953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10679 (p : Pattern) (ha : d87918 p = 1) (hb : d88959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87909 q = 1) (hb : d88954 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87909, d88954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10678 q ha hb
    | true =>
      simp only [d87909, d88954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87910 q = 1) (hb : d88955 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87910, d88955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87910, d88955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87914 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87915 q = 1) (hb : d88956 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87915, d88956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87915, d88956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87916 q = 1) (hb : d88957 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87916, d88957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87916, d88957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87917 q = 1) (hb : d88958 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87917, d88958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87917, d88958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87918 q = 1) (hb : d88959 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87918, d88959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87918, d88959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10680 (p : Pattern) (ha : d87943 p = 1) (hb : d88929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87909 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10672 q ha hb
    | true =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87910 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87914 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87915 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87916 q = 1) (hb : d88907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87916, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87916, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87942 q = 1) (hb : d88928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87942, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87942, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87943 q = 1) (hb : d88929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87943, d88929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87943, d88929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10681 (p : Pattern) (ha : d87952 p = 1) (hb : d88936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87909 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10672 q ha hb
    | true =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87910 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87914 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87915 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87950 q = 1) (hb : d88934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87950, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87950, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87951 q = 1) (hb : d88935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87951, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87951, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87952 q = 1) (hb : d88936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87952, d88936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87952, d88936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10682 (p : Pattern) (ha : d87962 p = 1) (hb : d88941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87961 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11909 q = 1) (hb : d53349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11910 q = 1) (hb : d87959 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d87959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11910, d87959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11911 q = 1) (hb : d87960 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d87960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11911, d87960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11912 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11913 q = 1) (hb : d87903 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d87903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11913, d87903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11914 q = 1) (hb : d87904 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d87904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11914, d87904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11915 q = 1) (hb : d87961 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d87961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11915, d87961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87961 q = 1) (hb : d88940 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d87962 q = 1) (hb : d88941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d87962, d88941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87962, d88941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10683 (p : Pattern) (ha : d87968 p = 1) (hb : d88947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87963 q = 1) (hb : d88942 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87963, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10682 q ha hb
    | true =>
      simp only [d87963, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87964 q = 1) (hb : d88943 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87964, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87964, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87910 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87965 q = 1) (hb : d88944 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87965, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87965, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87966 q = 1) (hb : d88945 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87966, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87966, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87967 q = 1) (hb : d88946 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87967, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87967, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87968 q = 1) (hb : d88947 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87968, d88947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87968, d88947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10684 (p : Pattern) (ha : d87974 p = 1) (hb : d88909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87909 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10672 q ha hb
    | true =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87910 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87971 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87971, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87971, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87972 q = 1) (hb : d88907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87972, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87972, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87973 q = 1) (hb : d88908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87973, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87973, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87974 q = 1) (hb : d88909 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87974, d88909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87974, d88909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10685 (p : Pattern) (ha : d87980 p = 1) (hb : d88966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87945 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87946 q = 1) (hb : d88930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87946, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10680 q ha hb
    | true =>
      simp only [d87946, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87947 q = 1) (hb : d88931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87947, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87947, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87948 q = 1) (hb : d88932 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87948, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87948, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87949 q = 1) (hb : d88933 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87949, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87949, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87955 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87956 q = 1) (hb : d88937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87956, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10681 q ha hb
    | true =>
      simp only [d87956, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87957 q = 1) (hb : d88938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87957, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87957, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87958 q = 1) (hb : d88939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87958, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87958, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87969 q = 1) (hb : d88960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87969, d88960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10683 q ha hb
    | true =>
      simp only [d87969, d88960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10679 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87923 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d87970 q = 1) (hb : d88961 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87970, d88961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87970, d88961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d87975 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87975, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10684 q ha hb
    | true =>
      simp only [d87975, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87976 q = 1) (hb : d88962 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87976, d88962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87976, d88962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87977 q = 1) (hb : d88963 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87977, d88963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87977, d88963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87978 q = 1) (hb : d88964 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87978, d88964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87978, d88964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d87979 q = 1) (hb : d88965 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87979, d88965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87979, d88965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87980 q = 1) (hb : d88966 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87980, d88966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87980, d88966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10686 (p : Pattern) (ha : d87931 p = 1) (hb : d88977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87909 q = 1) (hb : d88954 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87909, d88954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10678 q ha hb
    | true =>
      simp only [d87909, d88954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87910 q = 1) (hb : d88955 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87910, d88955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87910, d88955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87914 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87915 q = 1) (hb : d88956 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87915, d88956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87915, d88956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87916 q = 1) (hb : d88957 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87916, d88957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87916, d88957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87917 q = 1) (hb : d88958 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87917, d88958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87917, d88958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87931 q = 1) (hb : d88977 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87931, d88977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87931, d88977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10687 (p : Pattern) (ha : d87981 p = 1) (hb : d88967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87909 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10672 q ha hb
    | true =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87910 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87914 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87915 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87916 q = 1) (hb : d88907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87916, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87916, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87942 q = 1) (hb : d88928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87942, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87942, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87981 q = 1) (hb : d88967 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87981, d88967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87981, d88967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10688 (p : Pattern) (ha : d87987 p = 1) (hb : d88972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87909 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10672 q ha hb
    | true =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87910 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87914 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87915 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87915, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87950 q = 1) (hb : d88934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87950, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87950, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87951 q = 1) (hb : d88935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87951, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87951, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87987 q = 1) (hb : d88972 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87987, d88972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87987, d88972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10689 (p : Pattern) (ha : d87992 p = 1) (hb : d88976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87963 q = 1) (hb : d88942 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87963, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10682 q ha hb
    | true =>
      simp only [d87963, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87964 q = 1) (hb : d88943 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87964, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87964, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87910 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87965 q = 1) (hb : d88944 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87965, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87965, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87966 q = 1) (hb : d88945 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87966, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87966, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87967 q = 1) (hb : d88946 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87967, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87967, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87992 q = 1) (hb : d88976 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87992, d88976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87992, d88976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10690 (p : Pattern) (ha : d87995 p = 1) (hb : d88918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87909 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10672 q ha hb
    | true =>
      simp only [d87909, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87910 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87910, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87971 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87971, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87971, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d87972 q = 1) (hb : d88907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87972, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87972, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87973 q = 1) (hb : d88908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87973, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87973, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87995 q = 1) (hb : d88918 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87995, d88918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87995, d88918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10691 (p : Pattern) (ha : d88001 p = 1) (hb : d88984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87945 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87946 q = 1) (hb : d88930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87946, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10680 q ha hb
    | true =>
      simp only [d87946, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87947 q = 1) (hb : d88931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87947, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87947, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87948 q = 1) (hb : d88932 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87948, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87948, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87949 q = 1) (hb : d88933 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87949, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87949, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87955 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87956 q = 1) (hb : d88937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87956, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10681 q ha hb
    | true =>
      simp only [d87956, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87957 q = 1) (hb : d88938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87957, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87957, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87958 q = 1) (hb : d88939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87958, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87958, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d87969 q = 1) (hb : d88960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87969, d88960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10683 q ha hb
    | true =>
      simp only [d87969, d88960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10679 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87923 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d87970 q = 1) (hb : d88961 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87970, d88961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87970, d88961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d87975 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87975, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10684 q ha hb
    | true =>
      simp only [d87975, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d87976 q = 1) (hb : d88962 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87976, d88962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87976, d88962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d87977 q = 1) (hb : d88963 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87977, d88963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87977, d88963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d87978 q = 1) (hb : d88964 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87978, d88964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87978, d88964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d87979 q = 1) (hb : d88965 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87979, d88965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87979, d88965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d87982 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d87983 q = 1) (hb : d88968 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87983, d88968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10687 q ha hb
    | true =>
      simp only [d87983, d88968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d87984 q = 1) (hb : d88969 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87984, d88969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87984, d88969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d87985 q = 1) (hb : d88970 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87985, d88970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d87985, d88970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d87986 q = 1) (hb : d88971 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87986, d88971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87986, d88971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d87988 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d87989 q = 1) (hb : d88973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87989, d88973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10688 q ha hb
    | true =>
      simp only [d87989, d88973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d87990 q = 1) (hb : d88974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87990, d88974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87990, d88974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d87991 q = 1) (hb : d88975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87991, d88975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d87991, d88975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d87993 q = 1) (hb : d88978 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87993, d88978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10689 q ha hb
    | true =>
      simp only [d87993, d88978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10686 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d87933 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d87994 q = 1) (hb : d88979 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87994, d88979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d87994, d88979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d87996 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87996, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10690 q ha hb
    | true =>
      simp only [d87996, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d87997 q = 1) (hb : d88980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87997, d88980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d87997, d88980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d87998 q = 1) (hb : d88981 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87998, d88981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d87998, d88981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d87999 q = 1) (hb : d88982 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87999, d88982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d87999, d88982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d88000 q = 1) (hb : d88983 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88000, d88983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d88000, d88983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d88001 q = 1) (hb : d88984 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88001, d88984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d88001, d88984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro10692 (p : Pattern) (ha : d88008 p = 1) (hb : d88991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87923 q = 1) (hb : d88986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87923, d88986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10679 q ha hb
    | true =>
      simp only [d87923, d88986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d87924 q = 1) (hb : d88987 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87924, d88987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87924, d88987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87925 q = 1) (hb : d88988 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87925, d88988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87925, d88988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87926 q = 1) (hb : d88989 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87926, d88989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87926, d88989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87927 q = 1) (hb : d88990 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87927, d88990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87927, d88990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d88007 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d88008 q = 1) (hb : d88991 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88008, d88991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88008, d88991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10693 (p : Pattern) (ha : d88021 p = 1) (hb : d88998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87993 q = 1) (hb : d88978 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87993, d88978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10689 q ha hb
    | true =>
      simp only [d87993, d88978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10686 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87994 q = 1) (hb : d88979 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87994, d88979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87994, d88979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87996 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87996, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10690 q ha hb
    | true =>
      simp only [d87996, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87997 q = 1) (hb : d88980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87997, d88980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87997, d88980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87998 q = 1) (hb : d88981 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87998, d88981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87998, d88981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88019 q = 1) (hb : d88996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88019, d88996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88019, d88996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88020 q = 1) (hb : d88997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88020, d88997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88020, d88997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88021 q = 1) (hb : d88998 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88021, d88998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88021, d88998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10694 (p : Pattern) (ha : d88034 p = 1) (hb : d89005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d88033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53516 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12080 q = 1) (hb : d53516 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12081 q = 1) (hb : d88029 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d88029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12081, d88029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12082 q = 1) (hb : d88030 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d88030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12082, d88030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12084 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12085 q = 1) (hb : d88031 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d88031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12085, d88031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12086 q = 1) (hb : d88032 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d88032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12086, d88032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12087 q = 1) (hb : d88033 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d88033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12087, d88033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88033 q = 1) (hb : d89004 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d89004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d89004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d88034 q = 1) (hb : d89005 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d88034, d89005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88034, d89005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro10695 (p : Pattern) (ha : d88046 p = 1) (hb : d89011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88035 q = 1) (hb : d89006 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d88035, d89006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10694 q ha hb
    | true =>
      simp only [d88035, d89006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88036 q = 1) (hb : d89007 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d88036, d89007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88036, d89007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88042 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88043 q = 1) (hb : d89008 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88043, d89008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88043, d89008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d88044 q = 1) (hb : d89009 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d88044, d89009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88044, d89009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88045 q = 1) (hb : d89010 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d88045, d89010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88045, d89010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d88046 q = 1) (hb : d89011 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d88046, d89011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88046, d89011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10696 (p : Pattern) (ha : d6642 p = 1) (hb : d53521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2341 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2342 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2343 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h8 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2347 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2348 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2349 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2350 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2350, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6642 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6642, d53521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6642, d53521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10697 (p : Pattern) (ha : d88040 p = 1) (hb : d89017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d88039 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53521 q = 1) (hb : d89012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10696 q hb ha
    | true =>
      simp only [d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88031 q = 1) (hb : d89013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88031, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88031, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88032 q = 1) (hb : d89014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88032, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88032, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d88038 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d88039 q = 1) (hb : d89015 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88039, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88039, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88039 q = 1) (hb : d89016 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d89016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d89016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88040 q = 1) (hb : d89017 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d88040, d89017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88040, d89017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10698 (p : Pattern) (ha : d88054 p = 1) (hb : d89023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88041 q = 1) (hb : d89018 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d88041, d89018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10697 q ha hb
    | true =>
      simp only [d88041, d89018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88042 q = 1) (hb : d89019 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d88042, d89019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88042, d89019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88050 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88051 q = 1) (hb : d89020 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88051, d89020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88051, d89020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d88052 q = 1) (hb : d89021 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d88052, d89021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88052, d89021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88053 q = 1) (hb : d89022 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d88053, d89022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88053, d89022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d88054 q = 1) (hb : d89023 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d88054, d89023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88054, d89023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10699 (p : Pattern) (ha : d88040 p = 1) (hb : d89027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d88039 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12084 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12085 q = 1) (hb : d88031 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d88031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12085, d88031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12086 q = 1) (hb : d88032 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d88032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12086, d88032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d88038 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12092 q = 1) (hb : d88039 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d88039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12092, d88039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88039 q = 1) (hb : d89026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d89026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d89026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d88040 q = 1) (hb : d89027 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d88040, d89027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88040, d89027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro10700 (p : Pattern) (ha : d88065 p = 1) (hb : d89033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88041 q = 1) (hb : d89028 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d88041, d89028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10699 q ha hb
    | true =>
      simp only [d88041, d89028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88042 q = 1) (hb : d89029 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d88042, d89029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88042, d89029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88062 q = 1) (hb : d89030 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88062, d89030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88062, d89030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88063 q = 1) (hb : d89031 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d88063, d89031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88063, d89031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88064 q = 1) (hb : d89032 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d88064, d89032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88064, d89032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88065 q = 1) (hb : d89033 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d88065, d89033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88065, d89033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10701 (p : Pattern) (ha : d88071 p = 1) (hb : d89039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88055 q = 1) (hb : d89024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d88055, d89024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10695 q ha hb
    | true =>
      simp only [d88055, d89024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10698 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88060 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88061 q = 1) (hb : d89025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88061, d89025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88061, d89025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88066 q = 1) (hb : d89034 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d88066, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10700 q ha hb
    | true =>
      simp only [d88066, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88067 q = 1) (hb : d89035 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88067, d89035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88067, d89035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88068 q = 1) (hb : d89036 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88068, d89036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88068, d89036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88069 q = 1) (hb : d89037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88069, d89037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88069, d89037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88070 q = 1) (hb : d89038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88070, d89038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88070, d89038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88071 q = 1) (hb : d89039 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88071, d89039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88071, d89039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10702 (p : Pattern) (ha : d88084 p = 1) (hb : d89045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87929 q = 1) (hb : d88916 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87929, d88916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87929, d88916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10674 q ha hb
  have h2 (q : Pattern) (ha : d87930 q = 1) (hb : d88917 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87930, d88917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87930, d88917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87939 q = 1) (hb : d88925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87939, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10674 q ha hb
    | true =>
      simp only [d87939, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10676 q ha hb
  have h4 (q : Pattern) (ha : d87940 q = 1) (hb : d88926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87940, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87940, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87941 q = 1) (hb : d88927 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87941, d88927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87941, d88927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88002 q = 1) (hb : d88985 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88002, d88985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10685 q ha hb
    | true =>
      simp only [d88002, d88985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10691 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d88014 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d88015 q = 1) (hb : d88992 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88015, d88992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10692 q ha hb
    | true =>
      simp only [d88015, d88992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d88016 q = 1) (hb : d88993 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88016, d88993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88016, d88993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88017 q = 1) (hb : d88994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d88017, d88994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88017, d88994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d88018 q = 1) (hb : d88995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d88018, d88995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88018, d88995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d88022 q = 1) (hb : d88999 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88022, d88999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88022, d88999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10693 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d88024 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d88025 q = 1) (hb : d89000 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88025, d89000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d88025, d89000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d88026 q = 1) (hb : d89001 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d88026, d89001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d88026, d89001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d88027 q = 1) (hb : d89002 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d88027, d89002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d88027, d89002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d88028 q = 1) (hb : d89003 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d88028, d89003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88028, d89003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d88072 q = 1) (hb : d89040 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88072, d89040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88072, d89040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10701 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d88079 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d88080 q = 1) (hb : d89041 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88080, d89041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d88080, d89041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d88081 q = 1) (hb : d89042 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d88081, d89042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d88081, d89042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d88082 q = 1) (hb : d89043 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d88082, d89043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d88082, d89043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d88083 q = 1) (hb : d89044 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d88083, d89044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d88083, d89044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d88084 q = 1) (hb : d89045 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d88084, d89045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d88084, d89045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro10703 (p : Pattern) (ha : d88090 p = 1) (hb : d89051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88085 q = 1) (hb : d89046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d88085, d89046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88085, d89046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10702 q ha hb
  have h2 (q : Pattern) (ha : d88086 q = 1) (hb : d89047 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d88086, d89047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88086, d89047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88087 q = 1) (hb : d89048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d88087, d89048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88087, d89048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88088 q = 1) (hb : d89049 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d88088, d89049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88088, d89049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88089 q = 1) (hb : d89050 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d88089, d89050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88089, d89050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88090 q = 1) (hb : d89051 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d88090, d89051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88090, d89051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10704 (p : Pattern) (ha : d88096 p = 1) (hb : d89057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d87329 q = 1) (hb : d88442 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d87329, d88442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10543 q ha hb
    | true =>
      simp only [d87329, d88442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10575 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87518 q = 1) (hb : d88593 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d87518, d88593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87518, d88593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10607 q ha hb
  have h3 (q : Pattern) (ha : d87519 q = 1) (hb : d88594 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d87519, d88594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87519, d88594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87708 q = 1) (hb : d88745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d87708, d88745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87708, d88745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10639 q ha hb
  have h5 (q : Pattern) (ha : d87709 q = 1) (hb : d88746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d87709, d88746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87709, d88746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87710 q = 1) (hb : d88747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d87710, d88747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87710, d88747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87899 q = 1) (hb : d88898 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d87899, d88898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87899, d88898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10671 q ha hb
  have h8 (q : Pattern) (ha : d87900 q = 1) (hb : d88899 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d87900, d88899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87900, d88899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87901 q = 1) (hb : d88900 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d87901, d88900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87901, d88900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87902 q = 1) (hb : d88901 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d87902, d88901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87902, d88901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88091 q = 1) (hb : d89052 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d88091, d89052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88091, d89052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10703 q ha hb
  have h12 (q : Pattern) (ha : d88092 q = 1) (hb : d89053 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d88092, d89053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88092, d89053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d88093 q = 1) (hb : d89054 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d88093, d89054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88093, d89054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88094 q = 1) (hb : d89055 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d88094, d89055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88094, d89055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d88095 q = 1) (hb : d89056 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d88095, d89056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88095, d89056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88096 q = 1) (hb : d89057 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d88096, d89057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d88096, d89057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro10705 (p : Pattern) (ha : d88102 p = 1) (hb : d89063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88097 q = 1) (hb : d89058 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d88097, d89058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10704 q ha hb
    | true =>
      simp only [d88097, d89058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88098 q = 1) (hb : d89059 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d88098, d89059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88098, d89059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88099 q = 1) (hb : d89060 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d88099, d89060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88099, d89060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88100 q = 1) (hb : d89061 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d88100, d89061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88100, d89061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88101 q = 1) (hb : d89062 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d88101, d89062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88101, d89062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88102 q = 1) (hb : d89063 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d88102, d89063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88102, d89063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10706 (p : Pattern) (ha : d88108 p = 1) (hb : d89069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88103 q = 1) (hb : d89064 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d88103, d89064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10705 q ha hb
    | true =>
      simp only [d88103, d89064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88104 q = 1) (hb : d89065 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d88104, d89065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88104, d89065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88105 q = 1) (hb : d89066 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d88105, d89066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88105, d89066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88106 q = 1) (hb : d89067 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d88106, d89067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88106, d89067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88107 q = 1) (hb : d89068 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d88107, d89068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88107, d89068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88108 q = 1) (hb : d89069 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d88108, d89069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88108, d89069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10707 (p : Pattern) (ha : d88114 p = 1) (hb : d89075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88109 q = 1) (hb : d89070 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d88109, d89070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10706 q ha hb
    | true =>
      simp only [d88109, d89070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88110 q = 1) (hb : d89071 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d88110, d89071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88110, d89071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88111 q = 1) (hb : d89072 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d88111, d89072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88111, d89072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88112 q = 1) (hb : d89073 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d88112, d89073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88112, d89073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88113 q = 1) (hb : d89074 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d88113, d89074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88113, d89074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88114 q = 1) (hb : d89075 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d88114, d89075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88114, d89075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10708 (p : Pattern) (ha : d88120 p = 1) (hb : d89081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88115 q = 1) (hb : d89076 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d88115, d89076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10707 q ha hb
    | true =>
      simp only [d88115, d89076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88116 q = 1) (hb : d89077 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d88116, d89077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88116, d89077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88117 q = 1) (hb : d89078 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d88117, d89078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88117, d89078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88118 q = 1) (hb : d89079 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d88118, d89079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88118, d89079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88119 q = 1) (hb : d89080 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d88119, d89080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88119, d89080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88120 q = 1) (hb : d89081 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d88120, d89081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88120, d89081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10709 (p : Pattern) (ha : d88126 p = 1) (hb : d89087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88121 q = 1) (hb : d89082 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d88121, d89082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10708 q ha hb
    | true =>
      simp only [d88121, d89082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88122 q = 1) (hb : d89083 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d88122, d89083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88122, d89083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88123 q = 1) (hb : d89084 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d88123, d89084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88123, d89084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88124 q = 1) (hb : d89085 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d88124, d89085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88124, d89085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88125 q = 1) (hb : d89086 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d88125, d89086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88125, d89086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88126 q = 1) (hb : d89087 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d88126, d89087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88126, d89087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10710 (p : Pattern) (ha : d88132 p = 1) (hb : d89093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88127 q = 1) (hb : d89088 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d88127, d89088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10709 q ha hb
    | true =>
      simp only [d88127, d89088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88128 q = 1) (hb : d89089 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d88128, d89089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88128, d89089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88129 q = 1) (hb : d89090 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d88129, d89090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88129, d89090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88130 q = 1) (hb : d89091 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d88130, d89091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88130, d89091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88131 q = 1) (hb : d89092 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d88131, d89092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88131, d89092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88132 q = 1) (hb : d89093 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d88132, d89093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88132, d89093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10711 (p : Pattern) (ha : d88138 p = 1) (hb : d89099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88133 q = 1) (hb : d89094 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d88133, d89094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10710 q ha hb
    | true =>
      simp only [d88133, d89094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88134 q = 1) (hb : d89095 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d88134, d89095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88134, d89095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88135 q = 1) (hb : d89096 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d88135, d89096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88135, d89096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88136 q = 1) (hb : d89097 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d88136, d89097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88136, d89097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88137 q = 1) (hb : d89098 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d88137, d89098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88137, d89098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88138 q = 1) (hb : d89099 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d88138, d89099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88138, d89099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10712 (p : Pattern) (ha : d53647 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10271 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10272 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10288 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10289 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10713 (p : Pattern) (ha : d82697 p = 1) (hb : d85724 p = 1) : d89102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5856 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10281 q ha hb
    | true =>
      simp only [d5856, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
  have h2 (q : Pattern) (ha : d5898 q = 1) (hb : d85724 q = 1) : d88202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5898, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5899 q = 1) (hb : d85724 q = 1) : d88203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5899, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5900 q = 1) (hb : d85724 q = 1) : d88204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5901 q = 1) (hb : d85724 q = 1) : d88205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82697 q = 1) (hb : d85724 q = 1) : d89102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82697, d89102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82697, d89102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10714 (p : Pattern) (ha : d82707 p = 1) (hb : d85724 p = 1) : d89112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5874 q = 1) (hb : d85724 q = 1) : d88178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5874, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10285 q ha hb
    | true =>
      simp only [d5874, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10268 q ha hb
  have h2 (q : Pattern) (ha : d82703 q = 1) (hb : d85724 q = 1) : d89108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82703, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82703, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82704 q = 1) (hb : d85724 q = 1) : d89109 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82704, d89109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82704, d89109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82705 q = 1) (hb : d85724 q = 1) : d89110 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82705, d89110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82705, d89110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82706 q = 1) (hb : d85724 q = 1) : d89111 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82706, d89111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82706, d89111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82707 q = 1) (hb : d85724 q = 1) : d89112 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82707, d89112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82707, d89112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10715 (p : Pattern) (ha : d82713 p = 1) (hb : d85724 p = 1) : d89118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5903 q = 1) (hb : d85724 q = 1) : d88207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10290 q ha hb
    | true =>
      simp only [d5903, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10291 q ha hb
  have h2 (q : Pattern) (ha : d5904 q = 1) (hb : d85724 q = 1) : d88208 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5904, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82695 q = 1) (hb : d85724 q = 1) : d89100 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82695, d89100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82695, d89100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82696 q = 1) (hb : d85724 q = 1) : d89101 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82696, d89101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82696, d89101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82698 q = 1) (hb : d85724 q = 1) : d89103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82698, d89103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82698, d89103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10713 q ha hb
  have h6 (q : Pattern) (ha : d82699 q = 1) (hb : d85724 q = 1) : d89104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82699, d89104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82699, d89104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82700 q = 1) (hb : d85724 q = 1) : d89105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82700, d89105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82700, d89105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82701 q = 1) (hb : d85724 q = 1) : d89106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82701, d89106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82701, d89106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82702 q = 1) (hb : d85724 q = 1) : d89107 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82702, d89107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82702, d89107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82708 q = 1) (hb : d85724 q = 1) : d89113 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82708, d89113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82708, d89113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10714 q ha hb
  have h11 (q : Pattern) (ha : d82709 q = 1) (hb : d85724 q = 1) : d89114 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82709, d89114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82709, d89114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82710 q = 1) (hb : d85724 q = 1) : d89115 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82710, d89115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82710, d89115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82711 q = 1) (hb : d85724 q = 1) : d89116 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82711, d89116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82711, d89116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82712 q = 1) (hb : d85724 q = 1) : d89117 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82712, d89117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82712, d89117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82713 q = 1) (hb : d85724 q = 1) : d89118 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82713, d89118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82713, d89118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10716 (p : Pattern) (ha : d82719 p = 1) (hb : d85724 p = 1) : d89124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10712 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82714 q = 1) (hb : d85724 q = 1) : d89119 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82714, d89119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82714, d89119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10715 q ha hb
  have h7 (q : Pattern) (ha : d82715 q = 1) (hb : d85724 q = 1) : d89120 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82715, d89120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82715, d89120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82716 q = 1) (hb : d85724 q = 1) : d89121 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82716, d89121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82716, d89121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82717 q = 1) (hb : d85724 q = 1) : d89122 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82717, d89122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82717, d89122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82718 q = 1) (hb : d85724 q = 1) : d89123 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82718, d89123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82718, d89123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82719 q = 1) (hb : d85724 q = 1) : d89124 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82719, d89124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82719, d89124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10717 (p : Pattern) (ha : d82722 p = 1) (hb : d85724 p = 1) : d89127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6000 q = 1) (hb : d85724 q = 1) : d88309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6000, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10319 q ha hb
    | true =>
      simp only [d6000, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10310 q ha hb
  have h2 (q : Pattern) (ha : d6001 q = 1) (hb : d85724 q = 1) : d88310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6001, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6002 q = 1) (hb : d85724 q = 1) : d88311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6002, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6003 q = 1) (hb : d85724 q = 1) : d88312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6004 q = 1) (hb : d85724 q = 1) : d88313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82722 q = 1) (hb : d85724 q = 1) : d89127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82722, d89127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82722, d89127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10718 (p : Pattern) (ha : d82733 p = 1) (hb : d85724 p = 1) : d89137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82728 q = 1) (hb : d85724 q = 1) : d88424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d82728, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10340 q ha hb
    | true =>
      simp only [d82728, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10314 q ha hb
  have h2 (q : Pattern) (ha : d82729 q = 1) (hb : d85724 q = 1) : d89133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82729, d89133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82729, d89133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82730 q = 1) (hb : d85724 q = 1) : d89134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82730, d89134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82730, d89134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82731 q = 1) (hb : d85724 q = 1) : d89135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82731, d89135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82731, d89135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82732 q = 1) (hb : d85724 q = 1) : d89136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82732, d89136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82732, d89136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82733 q = 1) (hb : d85724 q = 1) : d89137 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82733, d89137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82733, d89137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10719 (p : Pattern) (ha : d82739 p = 1) (hb : d85724 p = 1) : d89143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6006 q = 1) (hb : d85724 q = 1) : d88315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10318 q ha hb
    | true =>
      simp only [d6006, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10320 q ha hb
  have h2 (q : Pattern) (ha : d6007 q = 1) (hb : d85724 q = 1) : d88316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6007, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82720 q = 1) (hb : d85724 q = 1) : d89125 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82720, d89125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82720, d89125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82721 q = 1) (hb : d85724 q = 1) : d89126 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82721, d89126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82721, d89126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82723 q = 1) (hb : d85724 q = 1) : d89128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82723, d89128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82723, d89128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10717 q ha hb
  have h6 (q : Pattern) (ha : d82724 q = 1) (hb : d85724 q = 1) : d89129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82724, d89129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82724, d89129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82725 q = 1) (hb : d85724 q = 1) : d89130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82725, d89130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82725, d89130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82726 q = 1) (hb : d85724 q = 1) : d89131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82726, d89131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82726, d89131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82727 q = 1) (hb : d85724 q = 1) : d89132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82727, d89132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82727, d89132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82734 q = 1) (hb : d85724 q = 1) : d89138 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82734, d89138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82734, d89138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10718 q ha hb
  have h11 (q : Pattern) (ha : d82735 q = 1) (hb : d85724 q = 1) : d89139 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82735, d89139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82735, d89139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82736 q = 1) (hb : d85724 q = 1) : d89140 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82736, d89140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82736, d89140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82737 q = 1) (hb : d85724 q = 1) : d89141 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82737, d89141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82737, d89141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82738 q = 1) (hb : d85724 q = 1) : d89142 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82738, d89142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82738, d89142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82739 q = 1) (hb : d85724 q = 1) : d89143 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82739, d89143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82739, d89143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10720 (p : Pattern) (ha : d82745 p = 1) (hb : d85724 p = 1) : d89149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82740 q = 1) (hb : d85724 q = 1) : d89144 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82740, d89144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82740, d89144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10719 q ha hb
  have h2 (q : Pattern) (ha : d82741 q = 1) (hb : d85724 q = 1) : d89145 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82741, d89145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82741, d89145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82742 q = 1) (hb : d85724 q = 1) : d89146 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82742, d89146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82742, d89146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82743 q = 1) (hb : d85724 q = 1) : d89147 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82743, d89147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82743, d89147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82744 q = 1) (hb : d85724 q = 1) : d89148 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82744, d89148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82744, d89148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82745 q = 1) (hb : d85724 q = 1) : d89149 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82745, d89149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82745, d89149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10721 (p : Pattern) (ha : d82749 p = 1) (hb : d85724 p = 1) : d89153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6128 q = 1) (hb : d85724 q = 1) : d88460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6128, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10359 q ha hb
    | true =>
      simp only [d6128, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10350 q ha hb
  have h2 (q : Pattern) (ha : d6129 q = 1) (hb : d85724 q = 1) : d88461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6129, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6130 q = 1) (hb : d85724 q = 1) : d88462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6130, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6131 q = 1) (hb : d85724 q = 1) : d88463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6132 q = 1) (hb : d85724 q = 1) : d88464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82749 q = 1) (hb : d85724 q = 1) : d89153 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82749, d89153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82749, d89153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10722 (p : Pattern) (ha : d82760 p = 1) (hb : d85724 p = 1) : d89163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82755 q = 1) (hb : d85724 q = 1) : d88575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d82755, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10384 q ha hb
    | true =>
      simp only [d82755, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10354 q ha hb
  have h2 (q : Pattern) (ha : d82756 q = 1) (hb : d85724 q = 1) : d89159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82756, d89159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82756, d89159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82757 q = 1) (hb : d85724 q = 1) : d89160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82757, d89160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82757, d89160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82758 q = 1) (hb : d85724 q = 1) : d89161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82758, d89161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82758, d89161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82759 q = 1) (hb : d85724 q = 1) : d89162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82759, d89162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82759, d89162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82760 q = 1) (hb : d85724 q = 1) : d89163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82760, d89163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82760, d89163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10723 (p : Pattern) (ha : d82766 p = 1) (hb : d85724 p = 1) : d89169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6134 q = 1) (hb : d85724 q = 1) : d88466 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10358 q ha hb
    | true =>
      simp only [d6134, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10360 q ha hb
  have h2 (q : Pattern) (ha : d6135 q = 1) (hb : d85724 q = 1) : d88467 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6135, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82747 q = 1) (hb : d85724 q = 1) : d89151 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82747, d89151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82747, d89151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82748 q = 1) (hb : d85724 q = 1) : d89152 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82748, d89152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82748, d89152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82750 q = 1) (hb : d85724 q = 1) : d89154 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82750, d89154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82750, d89154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10721 q ha hb
  have h6 (q : Pattern) (ha : d82751 q = 1) (hb : d85724 q = 1) : d89155 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82751, d89155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82751, d89155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82752 q = 1) (hb : d85724 q = 1) : d89156 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82752, d89156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82752, d89156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82753 q = 1) (hb : d85724 q = 1) : d89157 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82753, d89157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82753, d89157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82754 q = 1) (hb : d85724 q = 1) : d89158 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82754, d89158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82754, d89158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82761 q = 1) (hb : d85724 q = 1) : d89164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82761, d89164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82761, d89164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10722 q ha hb
  have h11 (q : Pattern) (ha : d82762 q = 1) (hb : d85724 q = 1) : d89165 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82762, d89165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82762, d89165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82763 q = 1) (hb : d85724 q = 1) : d89166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82763, d89166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82763, d89166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82764 q = 1) (hb : d85724 q = 1) : d89167 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82764, d89167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82764, d89167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82765 q = 1) (hb : d85724 q = 1) : d89168 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82765, d89168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82765, d89168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82766 q = 1) (hb : d85724 q = 1) : d89169 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82766, d89169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82766, d89169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10724 (p : Pattern) (ha : d82772 p = 1) (hb : d85724 p = 1) : d89175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82767 q = 1) (hb : d85724 q = 1) : d89170 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82767, d89170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82767, d89170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10723 q ha hb
  have h2 (q : Pattern) (ha : d82768 q = 1) (hb : d85724 q = 1) : d89171 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82768, d89171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82768, d89171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82769 q = 1) (hb : d85724 q = 1) : d89172 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82769, d89172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82769, d89172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82770 q = 1) (hb : d85724 q = 1) : d89173 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82770, d89173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82770, d89173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82771 q = 1) (hb : d85724 q = 1) : d89174 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82771, d89174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82771, d89174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82772 q = 1) (hb : d85724 q = 1) : d89175 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82772, d89175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82772, d89175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10725 (p : Pattern) (ha : d82777 p = 1) (hb : d85724 p = 1) : d89180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6267 q = 1) (hb : d85724 q = 1) : d88612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6267, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10399 q ha hb
    | true =>
      simp only [d6267, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10390 q ha hb
  have h2 (q : Pattern) (ha : d6268 q = 1) (hb : d85724 q = 1) : d88613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6268, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6269 q = 1) (hb : d85724 q = 1) : d88614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6269, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6270 q = 1) (hb : d85724 q = 1) : d88615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6271 q = 1) (hb : d85724 q = 1) : d88616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82777 q = 1) (hb : d85724 q = 1) : d89180 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82777, d89180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82777, d89180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10726 (p : Pattern) (ha : d82788 p = 1) (hb : d85724 p = 1) : d89190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82783 q = 1) (hb : d85724 q = 1) : d88727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d82783, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10424 q ha hb
    | true =>
      simp only [d82783, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10394 q ha hb
  have h2 (q : Pattern) (ha : d82784 q = 1) (hb : d85724 q = 1) : d89186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82784, d89186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82784, d89186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82785 q = 1) (hb : d85724 q = 1) : d89187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82785, d89187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82785, d89187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82786 q = 1) (hb : d85724 q = 1) : d89188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82786, d89188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82786, d89188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82787 q = 1) (hb : d85724 q = 1) : d89189 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82787, d89189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82787, d89189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82788 q = 1) (hb : d85724 q = 1) : d89190 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82788, d89190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82788, d89190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10727 (p : Pattern) (ha : d82794 p = 1) (hb : d85724 p = 1) : d89196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6273 q = 1) (hb : d85724 q = 1) : d88618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10398 q ha hb
    | true =>
      simp only [d6273, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10400 q ha hb
  have h2 (q : Pattern) (ha : d6274 q = 1) (hb : d85724 q = 1) : d88619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6274, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82775 q = 1) (hb : d85724 q = 1) : d89178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82775, d89178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82775, d89178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82776 q = 1) (hb : d85724 q = 1) : d89179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82776, d89179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82776, d89179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82778 q = 1) (hb : d85724 q = 1) : d89181 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82778, d89181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82778, d89181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10725 q ha hb
  have h6 (q : Pattern) (ha : d82779 q = 1) (hb : d85724 q = 1) : d89182 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82779, d89182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82779, d89182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82780 q = 1) (hb : d85724 q = 1) : d89183 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82780, d89183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82780, d89183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82781 q = 1) (hb : d85724 q = 1) : d89184 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82781, d89184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82781, d89184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82782 q = 1) (hb : d85724 q = 1) : d89185 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82782, d89185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82782, d89185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82789 q = 1) (hb : d85724 q = 1) : d89191 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82789, d89191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82789, d89191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10726 q ha hb
  have h11 (q : Pattern) (ha : d82790 q = 1) (hb : d85724 q = 1) : d89192 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82790, d89192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82790, d89192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82791 q = 1) (hb : d85724 q = 1) : d89193 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82791, d89193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82791, d89193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82792 q = 1) (hb : d85724 q = 1) : d89194 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82792, d89194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82792, d89194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82793 q = 1) (hb : d85724 q = 1) : d89195 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82793, d89195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82793, d89195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82794 q = 1) (hb : d85724 q = 1) : d89196 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82794, d89196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82794, d89196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10728 (p : Pattern) (ha : d82800 p = 1) (hb : d85724 p = 1) : d89202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82795 q = 1) (hb : d85724 q = 1) : d89197 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82795, d89197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82795, d89197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10727 q ha hb
  have h2 (q : Pattern) (ha : d82796 q = 1) (hb : d85724 q = 1) : d89198 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82796, d89198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82796, d89198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82797 q = 1) (hb : d85724 q = 1) : d89199 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82797, d89199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82797, d89199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82798 q = 1) (hb : d85724 q = 1) : d89200 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82798, d89200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82798, d89200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82799 q = 1) (hb : d85724 q = 1) : d89201 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82799, d89201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82799, d89201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82800 q = 1) (hb : d85724 q = 1) : d89202 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82800, d89202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82800, d89202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10729 (p : Pattern) (ha : d82806 p = 1) (hb : d85724 p = 1) : d89208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6413 q = 1) (hb : d85724 q = 1) : d88765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6413, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10439 q ha hb
    | true =>
      simp only [d6413, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10430 q ha hb
  have h2 (q : Pattern) (ha : d6414 q = 1) (hb : d85724 q = 1) : d88766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6414, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6415 q = 1) (hb : d85724 q = 1) : d88767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6415, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6416 q = 1) (hb : d85724 q = 1) : d88768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6417 q = 1) (hb : d85724 q = 1) : d88769 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82806 q = 1) (hb : d85724 q = 1) : d89208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82806, d89208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82806, d89208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10730 (p : Pattern) (ha : d82817 p = 1) (hb : d85724 p = 1) : d89218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82812 q = 1) (hb : d85724 q = 1) : d88880 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d82812, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10464 q ha hb
    | true =>
      simp only [d82812, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10434 q ha hb
  have h2 (q : Pattern) (ha : d82813 q = 1) (hb : d85724 q = 1) : d89214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82813, d89214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82813, d89214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82814 q = 1) (hb : d85724 q = 1) : d89215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82814, d89215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82814, d89215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82815 q = 1) (hb : d85724 q = 1) : d89216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82815, d89216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82815, d89216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82816 q = 1) (hb : d85724 q = 1) : d89217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82816, d89217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82816, d89217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82817 q = 1) (hb : d85724 q = 1) : d89218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82817, d89218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82817, d89218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10731 (p : Pattern) (ha : d82823 p = 1) (hb : d85724 p = 1) : d89224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6419 q = 1) (hb : d85724 q = 1) : d88771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10438 q ha hb
    | true =>
      simp only [d6419, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10440 q ha hb
  have h2 (q : Pattern) (ha : d6420 q = 1) (hb : d85724 q = 1) : d88772 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6420, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82804 q = 1) (hb : d85724 q = 1) : d89206 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82804, d89206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82804, d89206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82805 q = 1) (hb : d85724 q = 1) : d89207 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82805, d89207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82805, d89207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82807 q = 1) (hb : d85724 q = 1) : d89209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82807, d89209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82807, d89209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10729 q ha hb
  have h6 (q : Pattern) (ha : d82808 q = 1) (hb : d85724 q = 1) : d89210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82808, d89210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82808, d89210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82809 q = 1) (hb : d85724 q = 1) : d89211 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82809, d89211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82809, d89211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82810 q = 1) (hb : d85724 q = 1) : d89212 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82810, d89212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82810, d89212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82811 q = 1) (hb : d85724 q = 1) : d89213 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82811, d89213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82811, d89213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82818 q = 1) (hb : d85724 q = 1) : d89219 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82818, d89219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82818, d89219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10730 q ha hb
  have h11 (q : Pattern) (ha : d82819 q = 1) (hb : d85724 q = 1) : d89220 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82819, d89220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82819, d89220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82820 q = 1) (hb : d85724 q = 1) : d89221 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82820, d89221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82820, d89221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82821 q = 1) (hb : d85724 q = 1) : d89222 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82821, d89222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82821, d89222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82822 q = 1) (hb : d85724 q = 1) : d89223 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82822, d89223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82822, d89223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82823 q = 1) (hb : d85724 q = 1) : d89224 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82823, d89224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82823, d89224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10732 (p : Pattern) (ha : d82829 p = 1) (hb : d85724 p = 1) : d89230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82824 q = 1) (hb : d85724 q = 1) : d89225 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82824, d89225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82824, d89225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10731 q ha hb
  have h2 (q : Pattern) (ha : d82825 q = 1) (hb : d85724 q = 1) : d89226 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82825, d89226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82825, d89226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82826 q = 1) (hb : d85724 q = 1) : d89227 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82826, d89227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82826, d89227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82827 q = 1) (hb : d85724 q = 1) : d89228 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82827, d89228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82827, d89228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82828 q = 1) (hb : d85724 q = 1) : d89229 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82828, d89229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82828, d89229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82829 q = 1) (hb : d85724 q = 1) : d89230 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82829, d89230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82829, d89230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10733 (p : Pattern) (ha : d82836 p = 1) (hb : d85724 p = 1) : d89237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6560 q = 1) (hb : d85724 q = 1) : d88919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6560, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10479 q ha hb
    | true =>
      simp only [d6560, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10470 q ha hb
  have h2 (q : Pattern) (ha : d6561 q = 1) (hb : d85724 q = 1) : d88920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6561, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6562 q = 1) (hb : d85724 q = 1) : d88921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6562, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6563 q = 1) (hb : d85724 q = 1) : d88922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6564 q = 1) (hb : d85724 q = 1) : d88923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82836 q = 1) (hb : d85724 q = 1) : d89237 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82836, d89237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82836, d89237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10734 (p : Pattern) (ha : d82847 p = 1) (hb : d85724 p = 1) : d89247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82842 q = 1) (hb : d85724 q = 1) : d89034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d82842, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10504 q ha hb
    | true =>
      simp only [d82842, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10474 q ha hb
  have h2 (q : Pattern) (ha : d82843 q = 1) (hb : d85724 q = 1) : d89243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82843, d89243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82843, d89243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82844 q = 1) (hb : d85724 q = 1) : d89244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82844, d89244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82844, d89244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82845 q = 1) (hb : d85724 q = 1) : d89245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82845, d89245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82845, d89245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82846 q = 1) (hb : d85724 q = 1) : d89246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82846, d89246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82846, d89246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82847 q = 1) (hb : d85724 q = 1) : d89247 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82847, d89247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82847, d89247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10735 (p : Pattern) (ha : d82853 p = 1) (hb : d85724 p = 1) : d89253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6566 q = 1) (hb : d85724 q = 1) : d88925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10478 q ha hb
    | true =>
      simp only [d6566, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10480 q ha hb
  have h2 (q : Pattern) (ha : d6567 q = 1) (hb : d85724 q = 1) : d88926 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6567, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82834 q = 1) (hb : d85724 q = 1) : d89235 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82834, d89235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82834, d89235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82835 q = 1) (hb : d85724 q = 1) : d89236 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82835, d89236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82835, d89236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82837 q = 1) (hb : d85724 q = 1) : d89238 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82837, d89238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82837, d89238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10733 q ha hb
  have h6 (q : Pattern) (ha : d82838 q = 1) (hb : d85724 q = 1) : d89239 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82838, d89239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82838, d89239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82839 q = 1) (hb : d85724 q = 1) : d89240 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82839, d89240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82839, d89240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82840 q = 1) (hb : d85724 q = 1) : d89241 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82840, d89241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82840, d89241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82841 q = 1) (hb : d85724 q = 1) : d89242 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82841, d89242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82841, d89242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82848 q = 1) (hb : d85724 q = 1) : d89248 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82848, d89248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82848, d89248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10734 q ha hb
  have h11 (q : Pattern) (ha : d82849 q = 1) (hb : d85724 q = 1) : d89249 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82849, d89249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82849, d89249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82850 q = 1) (hb : d85724 q = 1) : d89250 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82850, d89250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82850, d89250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82851 q = 1) (hb : d85724 q = 1) : d89251 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82851, d89251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82851, d89251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82852 q = 1) (hb : d85724 q = 1) : d89252 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82852, d89252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82852, d89252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82853 q = 1) (hb : d85724 q = 1) : d89253 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82853, d89253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82853, d89253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10736 (p : Pattern) (ha : d82859 p = 1) (hb : d85724 p = 1) : d89259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82854 q = 1) (hb : d85724 q = 1) : d89254 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82854, d89254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82854, d89254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10735 q ha hb
  have h2 (q : Pattern) (ha : d82855 q = 1) (hb : d85724 q = 1) : d89255 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82855, d89255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82855, d89255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82856 q = 1) (hb : d85724 q = 1) : d89256 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82856, d89256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82856, d89256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82857 q = 1) (hb : d85724 q = 1) : d89257 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82857, d89257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82857, d89257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82858 q = 1) (hb : d85724 q = 1) : d89258 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82858, d89258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82858, d89258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82859 q = 1) (hb : d85724 q = 1) : d89259 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82859, d89259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82859, d89259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10737 (p : Pattern) (ha : d82865 p = 1) (hb : d85724 p = 1) : d89265 p = 1 := by
  have h0 (q : Pattern) (ha : d82746 q = 1) (hb : d85724 q = 1) : d89150 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82746, d89150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10716 q ha hb
    | true =>
      simp only [d82746, d89150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10720 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82773 q = 1) (hb : d85724 q = 1) : d89176 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82773, d89176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82773, d89176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10724 q ha hb
  have h3 (q : Pattern) (ha : d82774 q = 1) (hb : d85724 q = 1) : d89177 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82774, d89177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82774, d89177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82801 q = 1) (hb : d85724 q = 1) : d89203 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82801, d89203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82801, d89203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10728 q ha hb
  have h5 (q : Pattern) (ha : d82802 q = 1) (hb : d85724 q = 1) : d89204 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82802, d89204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82802, d89204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82803 q = 1) (hb : d85724 q = 1) : d89205 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82803, d89205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82803, d89205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82830 q = 1) (hb : d85724 q = 1) : d89231 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82830, d89231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82830, d89231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10732 q ha hb
  have h8 (q : Pattern) (ha : d82831 q = 1) (hb : d85724 q = 1) : d89232 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82831, d89232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82831, d89232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82832 q = 1) (hb : d85724 q = 1) : d89233 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82832, d89233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82832, d89233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82833 q = 1) (hb : d85724 q = 1) : d89234 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82833, d89234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82833, d89234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82860 q = 1) (hb : d85724 q = 1) : d89260 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82860, d89260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82860, d89260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10736 q ha hb
  have h12 (q : Pattern) (ha : d82861 q = 1) (hb : d85724 q = 1) : d89261 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82861, d89261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82861, d89261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82862 q = 1) (hb : d85724 q = 1) : d89262 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82862, d89262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82862, d89262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82863 q = 1) (hb : d85724 q = 1) : d89263 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82863, d89263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82863, d89263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82864 q = 1) (hb : d85724 q = 1) : d89264 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d82864, d89264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82864, d89264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82865 q = 1) (hb : d85724 q = 1) : d89265 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d82865, d89265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82865, d89265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro10738 (p : Pattern) (ha : d82871 p = 1) (hb : d85724 p = 1) : d89271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82866 q = 1) (hb : d85724 q = 1) : d89266 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d82866, d89266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10737 q ha hb
    | true =>
      simp only [d82866, d89266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82867 q = 1) (hb : d85724 q = 1) : d89267 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d82867, d89267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82867, d89267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82868 q = 1) (hb : d85724 q = 1) : d89268 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d82868, d89268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82868, d89268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82869 q = 1) (hb : d85724 q = 1) : d89269 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d82869, d89269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82869, d89269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82870 q = 1) (hb : d85724 q = 1) : d89270 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d82870, d89270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82870, d89270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82871 q = 1) (hb : d85724 q = 1) : d89271 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d82871, d89271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82871, d89271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10739 (p : Pattern) (ha : d82877 p = 1) (hb : d85724 p = 1) : d89277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82872 q = 1) (hb : d85724 q = 1) : d89272 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d82872, d89272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10738 q ha hb
    | true =>
      simp only [d82872, d89272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82873 q = 1) (hb : d85724 q = 1) : d89273 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d82873, d89273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82873, d89273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82874 q = 1) (hb : d85724 q = 1) : d89274 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d82874, d89274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82874, d89274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82875 q = 1) (hb : d85724 q = 1) : d89275 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d82875, d89275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82875, d89275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82876 q = 1) (hb : d85724 q = 1) : d89276 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d82876, d89276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82876, d89276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82877 q = 1) (hb : d85724 q = 1) : d89277 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d82877, d89277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82877, d89277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10740 (p : Pattern) (ha : d82883 p = 1) (hb : d85724 p = 1) : d89283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82878 q = 1) (hb : d85724 q = 1) : d89278 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82878, d89278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10739 q ha hb
    | true =>
      simp only [d82878, d89278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82879 q = 1) (hb : d85724 q = 1) : d89279 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82879, d89279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82879, d89279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82880 q = 1) (hb : d85724 q = 1) : d89280 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82880, d89280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82880, d89280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82881 q = 1) (hb : d85724 q = 1) : d89281 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82881, d89281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82881, d89281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82882 q = 1) (hb : d85724 q = 1) : d89282 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82882, d89282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82882, d89282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82883 q = 1) (hb : d85724 q = 1) : d89283 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82883, d89283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82883, d89283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10741 (p : Pattern) (ha : d82889 p = 1) (hb : d85724 p = 1) : d89289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82884 q = 1) (hb : d85724 q = 1) : d89284 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82884, d89284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10740 q ha hb
    | true =>
      simp only [d82884, d89284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82885 q = 1) (hb : d85724 q = 1) : d89285 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82885, d89285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82885, d89285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82886 q = 1) (hb : d85724 q = 1) : d89286 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82886, d89286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82886, d89286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82887 q = 1) (hb : d85724 q = 1) : d89287 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82887, d89287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82887, d89287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82888 q = 1) (hb : d85724 q = 1) : d89288 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82888, d89288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82888, d89288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82889 q = 1) (hb : d85724 q = 1) : d89289 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82889, d89289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82889, d89289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10742 (p : Pattern) (ha : d82895 p = 1) (hb : d85724 p = 1) : d89295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82890 q = 1) (hb : d85724 q = 1) : d89290 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82890, d89290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10741 q ha hb
    | true =>
      simp only [d82890, d89290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82891 q = 1) (hb : d85724 q = 1) : d89291 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82891, d89291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82891, d89291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82892 q = 1) (hb : d85724 q = 1) : d89292 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82892, d89292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82892, d89292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82893 q = 1) (hb : d85724 q = 1) : d89293 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82893, d89293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82893, d89293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82894 q = 1) (hb : d85724 q = 1) : d89294 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82894, d89294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82894, d89294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82895 q = 1) (hb : d85724 q = 1) : d89295 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82895, d89295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82895, d89295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10743 (p : Pattern) (ha : d82901 p = 1) (hb : d85724 p = 1) : d89301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82896 q = 1) (hb : d85724 q = 1) : d89296 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82896, d89296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10742 q ha hb
    | true =>
      simp only [d82896, d89296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82897 q = 1) (hb : d85724 q = 1) : d89297 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82897, d89297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82897, d89297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82898 q = 1) (hb : d85724 q = 1) : d89298 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82898, d89298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82898, d89298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82899 q = 1) (hb : d85724 q = 1) : d89299 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82899, d89299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82899, d89299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82900 q = 1) (hb : d85724 q = 1) : d89300 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82900, d89300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82900, d89300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82901 q = 1) (hb : d85724 q = 1) : d89301 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82901, d89301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82901, d89301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10744 (p : Pattern) (ha : d82907 p = 1) (hb : d85724 p = 1) : d89307 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82902 q = 1) (hb : d85724 q = 1) : d89302 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82902, d89302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10743 q ha hb
    | true =>
      simp only [d82902, d89302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82903 q = 1) (hb : d85724 q = 1) : d89303 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82903, d89303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82903, d89303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82904 q = 1) (hb : d85724 q = 1) : d89304 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82904, d89304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82904, d89304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82905 q = 1) (hb : d85724 q = 1) : d89305 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82905, d89305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82905, d89305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82906 q = 1) (hb : d85724 q = 1) : d89306 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82906, d89306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82906, d89306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82907 q = 1) (hb : d85724 q = 1) : d89307 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82907, d89307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82907, d89307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10745 (p : Pattern) (ha : d87146 p = 1) (hb : d88199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87124 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87141 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87054 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
    | true =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d87142 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87142, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d87142, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87055 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87143 q = 1) (hb : d88196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87143, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87143, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87144 q = 1) (hb : d88197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87144, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87144, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87145 q = 1) (hb : d88198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87145, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87145, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87146 q = 1) (hb : d88199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87146, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87146, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10746 (p : Pattern) (ha : d87162 p = 1) (hb : d88206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87124 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87141 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87054 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10517 q ha hb
    | true =>
      simp only [d87054, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87142 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87142, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87142, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87055 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87143 q = 1) (hb : d88196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87143, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87143, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87144 q = 1) (hb : d88197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87144, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87144, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87145 q = 1) (hb : d88198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87145, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87145, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d87151 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87155 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d87157 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d87061 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10519 q ha hb
    | true =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d87158 q = 1) (hb : d88202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87158, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d87158, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d87062 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d87159 q = 1) (hb : d88203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87159, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d87159, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d87160 q = 1) (hb : d88204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87160, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d87160, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d87161 q = 1) (hb : d88205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87161, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d87161, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d87162 q = 1) (hb : d88206 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87162, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87162, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10747 (p : Pattern) (ha : d87171 p = 1) (hb : d89102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87157 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87061 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10519 q ha hb
    | true =>
      simp only [d87061, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87158 q = 1) (hb : d88202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87158, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87158, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d87062 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87159 q = 1) (hb : d88203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87159, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87159, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87169 q = 1) (hb : d88204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87169, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87169, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87170 q = 1) (hb : d88205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87170, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87170, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87171 q = 1) (hb : d89102 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87171, d89102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87171, d89102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10748 (p : Pattern) (ha : d87192 p = 1) (hb : d89112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87187 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87087 q = 1) (hb : d88178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87087, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10523 q ha hb
    | true =>
      simp only [d87087, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d87188 q = 1) (hb : d89108 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87188, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87188, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d87088 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87189 q = 1) (hb : d89109 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87189, d89109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87189, d89109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87190 q = 1) (hb : d89110 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87190, d89110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87190, d89110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87191 q = 1) (hb : d89111 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87191, d89111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87191, d89111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87192 q = 1) (hb : d89112 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87192, d89112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87192, d89112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10749 (p : Pattern) (ha : d87198 p = 1) (hb : d89118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87118 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87163 q = 1) (hb : d88207 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87163, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10745 q ha hb
    | true =>
      simp only [d87163, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10746 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87166 q = 1) (hb : d88208 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87166, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87166, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87167 q = 1) (hb : d89100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87167, d89100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87167, d89100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87168 q = 1) (hb : d89101 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87168, d89101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87168, d89101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87172 q = 1) (hb : d89103 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87172, d89103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d87172, d89103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10747 q ha hb
  have h8 (q : Pattern) (ha : d87173 q = 1) (hb : d89104 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87173, d89104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87173, d89104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d87174 q = 1) (hb : d89105 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87174, d89105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d87174, d89105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d87175 q = 1) (hb : d89106 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87175, d89106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87175, d89106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d87176 q = 1) (hb : d89107 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87176, d89107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87176, d89107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d87193 q = 1) (hb : d89113 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87193, d89113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d87193, d89113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10748 q ha hb
  have h13 (q : Pattern) (ha : d87194 q = 1) (hb : d89114 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87194, d89114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87194, d89114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d87195 q = 1) (hb : d89115 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87195, d89115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87195, d89115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d87196 q = 1) (hb : d89116 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87196, d89116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d87196, d89116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d87197 q = 1) (hb : d89117 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87197, d89117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87197, d89117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d87198 q = 1) (hb : d89118 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87198, d89118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d87198, d89118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
end NetHack.Soko22Hazard87
