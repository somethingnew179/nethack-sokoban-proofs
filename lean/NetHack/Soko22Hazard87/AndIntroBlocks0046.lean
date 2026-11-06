import NetHack.Soko22Hazard87.AndIntroBlocks0045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro11500 (p : Pattern) (ha : d7036 p = 1) (hb : d81824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7034 q = 1) (hb : d81822 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d81822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d81822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5140 q = 1) (hb : d69227 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d69227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q ha hb
    | true =>
      simp only [d5140, d69227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7965 q ha hb
  have h6 (q : Pattern) (ha : d5141 q = 1) (hb : d69228 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d69228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d69228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5142 q = 1) (hb : d69229 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d69229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d69229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5143 q = 1) (hb : d69230 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d69230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5143, d69230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7035 q = 1) (hb : d81823 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7035, d81823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7035, d81823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7036 q = 1) (hb : d81824 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7036, d81824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7036, d81824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11501 (p : Pattern) (ha : d92972 p = 1) (hb : d93748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d81825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11500 q ha hb
    | true =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d81826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d81826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d81826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92969 q = 1) (hb : d93745 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92969, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92969, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92970 q = 1) (hb : d93746 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92970, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92970, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92971 q = 1) (hb : d93747 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92971, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92971, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92972 q = 1) (hb : d93748 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92972, d93748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92972, d93748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11502 (p : Pattern) (ha : d92984 p = 1) (hb : d93754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92950 q = 1) (hb : d93731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92950, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11496 q ha hb
    | true =>
      simp only [d92950, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q hb ha
  have h2 (q : Pattern) (ha : d92951 q = 1) (hb : d93732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92951, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92951, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92952 q = 1) (hb : d93733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92952, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92952, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92953 q = 1) (hb : d93734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92953, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92953, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92957 q = 1) (hb : d93738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92957, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11497 q ha hb
    | true =>
      simp only [d92957, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q hb ha
  have h6 (q : Pattern) (ha : d92958 q = 1) (hb : d93739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92958, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92958, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92959 q = 1) (hb : d93740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92959, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92959, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92973 q = 1) (hb : d93749 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92973, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11499 q ha hb
    | true =>
      simp only [d92973, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11501 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92930 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92974 q = 1) (hb : d93750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92974, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8977 q = 1) (hb : d92979 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d92979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11495 q ha hb
    | true =>
      simp only [d8977, d92979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8978 q = 1) (hb : d92980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d92980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8978, d92980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92981 q = 1) (hb : d93751 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92981, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92982 q = 1) (hb : d93752 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92982, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92983 q = 1) (hb : d93753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92983, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92984 q = 1) (hb : d93754 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92984, d93754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92984, d93754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro11503 (p : Pattern) (ha : d8998 p = 1) (hb : d92998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11490 q ha hb
    | true =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d92975 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d92975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d92975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d92976 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d92976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d92976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d92977 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d92977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d92977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8998 q = 1) (hb : d92998 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8998, d92998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8998, d92998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11504 (p : Pattern) (ha : d92985 p = 1) (hb : d93755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11490 q ha hb
    | true =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8973 q = 1) (hb : d92926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8974 q = 1) (hb : d92927 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d92927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8974, d92927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92948 q = 1) (hb : d93729 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92948, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92948, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92985 q = 1) (hb : d93755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92985, d93755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92985, d93755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11505 (p : Pattern) (ha : d92990 p = 1) (hb : d93760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11490 q ha hb
    | true =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8973 q = 1) (hb : d92926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92954 q = 1) (hb : d93735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92954, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92954, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92955 q = 1) (hb : d93736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92955, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92955, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92990 q = 1) (hb : d93760 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92990, d93760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92990, d93760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11506 (p : Pattern) (ha : d92994 p = 1) (hb : d93764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d92963 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d92963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11498 q ha hb
    | true =>
      simp only [d8951, d92963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d92964 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d92964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d92964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81826 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92965 q = 1) (hb : d93741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92965, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92965, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92966 q = 1) (hb : d93742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92966, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92966, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92967 q = 1) (hb : d93743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92967, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92967, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92994 q = 1) (hb : d93764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92994, d93764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92994, d93764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11507 (p : Pattern) (ha : d92995 p = 1) (hb : d93765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d81825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11500 q ha hb
    | true =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d81826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d81826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d81826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92969 q = 1) (hb : d93745 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92969, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92969, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92970 q = 1) (hb : d93746 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92970, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92970, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92971 q = 1) (hb : d93747 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92971, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92971, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92995 q = 1) (hb : d93765 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92995, d93765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92995, d93765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11508 (p : Pattern) (ha : d93004 p = 1) (hb : d93771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92950 q = 1) (hb : d93731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92950, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11496 q ha hb
    | true =>
      simp only [d92950, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q hb ha
  have h2 (q : Pattern) (ha : d92951 q = 1) (hb : d93732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92951, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92951, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92952 q = 1) (hb : d93733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92952, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92952, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92953 q = 1) (hb : d93734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92953, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92953, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92957 q = 1) (hb : d93738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92957, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11497 q ha hb
    | true =>
      simp only [d92957, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q hb ha
  have h6 (q : Pattern) (ha : d92958 q = 1) (hb : d93739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92958, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92958, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92959 q = 1) (hb : d93740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92959, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92959, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92973 q = 1) (hb : d93749 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92973, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11499 q ha hb
    | true =>
      simp only [d92973, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11501 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92930 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92974 q = 1) (hb : d93750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92974, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8977 q = 1) (hb : d92979 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d92979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11495 q ha hb
    | true =>
      simp only [d8977, d92979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8978 q = 1) (hb : d92980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d92980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8978, d92980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92981 q = 1) (hb : d93751 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92981, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92982 q = 1) (hb : d93752 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92982, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92983 q = 1) (hb : d93753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92983, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92986 q = 1) (hb : d93756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92986, d93756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11504 q ha hb
    | true =>
      simp only [d92986, d93756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro249 q hb ha
  have h17 (q : Pattern) (ha : d92987 q = 1) (hb : d93757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92987, d93757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92987, d93757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92988 q = 1) (hb : d93758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92988, d93758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92988, d93758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92989 q = 1) (hb : d93759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92989, d93759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92989, d93759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92991 q = 1) (hb : d93761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92991, d93761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11505 q ha hb
    | true =>
      simp only [d92991, d93761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q hb ha
  have h21 (q : Pattern) (ha : d92992 q = 1) (hb : d93762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92992, d93762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92992, d93762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92993 q = 1) (hb : d93763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92993, d93763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92993, d93763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92996 q = 1) (hb : d93766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92996, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11506 q ha hb
    | true =>
      simp only [d92996, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11507 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92939 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92997 q = 1) (hb : d93767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92997, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8999 q = 1) (hb : d92999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d92999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11503 q ha hb
    | true =>
      simp only [d8999, d92999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d9000 q = 1) (hb : d93000 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d93000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9000, d93000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d93001 q = 1) (hb : d93768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d93001, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d93002 q = 1) (hb : d93769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93002, d93769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d93002, d93769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d93003 q = 1) (hb : d93770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93003, d93770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93003, d93770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d93004 q = 1) (hb : d93771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93004, d93771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93004, d93771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro11509 (p : Pattern) (ha : d93011 p = 1) (hb : d93778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93006 q = 1) (hb : d93773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93006, d93773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11501 q ha hb
    | true =>
      simp only [d93006, d93773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d93007 q = 1) (hb : d93774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93007, d93774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93007, d93774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93008 q = 1) (hb : d93775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93008, d93775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93008, d93775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93009 q = 1) (hb : d93776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93009, d93776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93009, d93776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93010 q = 1) (hb : d93777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93010, d93777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93010, d93777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d93011 q = 1) (hb : d93778 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93011, d93778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93011, d93778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro11510 (p : Pattern) (ha : d93018 p = 1) (hb : d93785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92996 q = 1) (hb : d93766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92996, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11506 q ha hb
    | true =>
      simp only [d92996, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11507 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92939 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92997 q = 1) (hb : d93767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92997, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8999 q = 1) (hb : d92999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d92999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11503 q ha hb
    | true =>
      simp only [d8999, d92999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9000 q = 1) (hb : d93000 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d93000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9000, d93000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d93001 q = 1) (hb : d93768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93001, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93016 q = 1) (hb : d93783 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93016, d93783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93016, d93783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93017 q = 1) (hb : d93784 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93017, d93784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93017, d93784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93018 q = 1) (hb : d93785 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93018, d93785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93018, d93785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11511 (p : Pattern) (ha : d9050 p = 1) (hb : d93039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7080 q = 1) (hb : d81868 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d81868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d81868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1889 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro226 q ha hb
  have h6 (q : Pattern) (ha : d1890 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1891 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1897 q = 1) (hb : d53223 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1897, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9049 q = 1) (hb : d93038 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9049, d93038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9049, d93038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9050 q = 1) (hb : d93039 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9050, d93039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9050, d93039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11512 (p : Pattern) (ha : d9056 p = 1) (hb : d93051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d93040 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d93040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11511 q ha hb
    | true =>
      simp only [d9051, d93040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d93041 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d93041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d93041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9053 q = 1) (hb : d93048 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9053, d93048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9053, d93048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9054 q = 1) (hb : d93049 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9054, d93049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9054, d93049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9055 q = 1) (hb : d93050 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9055, d93050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9055, d93050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9056 q = 1) (hb : d93051 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9056, d93051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9056, d93051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11513 (p : Pattern) (ha : d9026 p = 1) (hb : d93026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1874 q = 1) (hb : d53200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro235 q ha hb
    | true =>
      simp only [d1874, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
  have h2 (q : Pattern) (ha : d1875 q = 1) (hb : d53201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1876 q = 1) (hb : d53202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9024 q = 1) (hb : d93024 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9024, d93024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9024, d93024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1879 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
  have h6 (q : Pattern) (ha : d1880 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1881 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7080 q = 1) (hb : d81868 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d81868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7080, d81868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9025 q = 1) (hb : d93025 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9025, d93025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9025, d93025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9026 q = 1) (hb : d93026 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9026, d93026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9026, d93026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11514 (p : Pattern) (ha : d93032 p = 1) (hb : d93794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9027 q = 1) (hb : d93027 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9027, d93027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11513 q ha hb
    | true =>
      simp only [d9027, d93027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9028 q = 1) (hb : d93028 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9028, d93028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9028, d93028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81872 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93029 q = 1) (hb : d93791 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93029, d93791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93029, d93791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d93030 q = 1) (hb : d93792 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93030, d93792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93030, d93792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93031 q = 1) (hb : d93793 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93031, d93793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93031, d93793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93032 q = 1) (hb : d93794 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93032, d93794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93032, d93794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11515 (p : Pattern) (ha : d7082 p = 1) (hb : d81870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7080 q = 1) (hb : d81868 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d81868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d81868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6502 q = 1) (hb : d76231 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d76231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q ha hb
    | true =>
      simp only [d6502, d76231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10901 q ha hb
  have h6 (q : Pattern) (ha : d6503 q = 1) (hb : d76232 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d76232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d76232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6504 q = 1) (hb : d76233 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d76233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d76233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6505 q = 1) (hb : d76234 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d76234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6505, d76234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7081 q = 1) (hb : d81869 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7081, d81869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7081, d81869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7082 q = 1) (hb : d81870 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7082, d81870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7082, d81870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11516 (p : Pattern) (ha : d93036 p = 1) (hb : d93798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7083 q = 1) (hb : d81871 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d81871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11515 q ha hb
    | true =>
      simp only [d7083, d81871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7084 q = 1) (hb : d81872 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d81872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d81872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93033 q = 1) (hb : d93795 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93033, d93795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93033, d93795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d93034 q = 1) (hb : d93796 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93034, d93796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93034, d93796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93035 q = 1) (hb : d93797 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93035, d93797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93035, d93797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93036 q = 1) (hb : d93798 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93036, d93798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93036, d93798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11517 (p : Pattern) (ha : d93057 p = 1) (hb : d93804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93037 q = 1) (hb : d93799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93037, d93799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11514 q ha hb
    | true =>
      simp only [d93037, d93799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11516 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93046 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93047 q = 1) (hb : d93800 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93047, d93800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93047, d93800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9057 q = 1) (hb : d93052 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9057, d93052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11512 q ha hb
    | true =>
      simp only [d9057, d93052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9058 q = 1) (hb : d93053 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9058, d93053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9058, d93053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d93054 q = 1) (hb : d93801 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93054, d93801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93054, d93801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93055 q = 1) (hb : d93802 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93055, d93802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93055, d93802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93056 q = 1) (hb : d93803 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93056, d93803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93056, d93803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93057 q = 1) (hb : d93804 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93057, d93804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93057, d93804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11518 (p : Pattern) (ha : d93063 p = 1) (hb : d93810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92936 q = 1) (hb : d93718 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92936, d93718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92936, d93718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11492 q ha hb
  have h2 (q : Pattern) (ha : d92937 q = 1) (hb : d93719 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92937, d93719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92937, d93719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92945 q = 1) (hb : d93726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92945, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11492 q ha hb
    | true =>
      simp only [d92945, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11494 q ha hb
  have h4 (q : Pattern) (ha : d92946 q = 1) (hb : d93727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92946, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92946, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92947 q = 1) (hb : d93728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92947, d93728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92947, d93728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93005 q = 1) (hb : d93772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93005, d93772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11502 q ha hb
    | true =>
      simp only [d93005, d93772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11508 q ha hb
  have h7 (q : Pattern) (ha : d93012 q = 1) (hb : d93779 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93012, d93779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11509 q ha hb
    | true =>
      simp only [d93012, d93779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q hb ha
  have h8 (q : Pattern) (ha : d93013 q = 1) (hb : d93780 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93013, d93780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93013, d93780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93014 q = 1) (hb : d93781 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93014, d93781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93014, d93781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d93015 q = 1) (hb : d93782 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93015, d93782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93015, d93782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93019 q = 1) (hb : d93786 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93019, d93786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93019, d93786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11510 q ha hb
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
  have h13 (q : Pattern) (ha : d93020 q = 1) (hb : d93787 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93020, d93787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93020, d93787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d93021 q = 1) (hb : d93788 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93021, d93788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93021, d93788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d93022 q = 1) (hb : d93789 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93022, d93789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d93022, d93789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d93023 q = 1) (hb : d93790 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93023, d93790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93023, d93790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93058 q = 1) (hb : d93805 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93058, d93805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93058, d93805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11517 q ha hb
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
  have h19 (q : Pattern) (ha : d93059 q = 1) (hb : d93806 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93059, d93806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93059, d93806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d93060 q = 1) (hb : d93807 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93060, d93807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93060, d93807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d93061 q = 1) (hb : d93808 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93061, d93808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d93061, d93808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d93062 q = 1) (hb : d93809 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93062, d93809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d93062, d93809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d93063 q = 1) (hb : d93810 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93063, d93810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93063, d93810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11519 (p : Pattern) (ha : d93069 p = 1) (hb : d93816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93064 q = 1) (hb : d93811 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93064, d93811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93064, d93811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11518 q ha hb
  have h2 (q : Pattern) (ha : d93065 q = 1) (hb : d93812 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93065, d93812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93065, d93812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93066 q = 1) (hb : d93813 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93066, d93813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93066, d93813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93067 q = 1) (hb : d93814 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93067, d93814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93067, d93814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93068 q = 1) (hb : d93815 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93068, d93815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93068, d93815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93069 q = 1) (hb : d93816 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93069, d93816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93069, d93816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11520 (p : Pattern) (ha : d9080 p = 1) (hb : d93075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7115 q = 1) (hb : d81903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d81903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d81903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2086 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro272 q ha hb
  have h6 (q : Pattern) (ha : d2087 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2088 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2090 q = 1) (hb : d53369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2090, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9079 q = 1) (hb : d93074 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9079, d93074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9079, d93074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9080 q = 1) (hb : d93075 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9080, d93075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9080, d93075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11521 (p : Pattern) (ha : d9145 p = 1) (hb : d93081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d93076 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11520 q ha hb
    | true =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d93077 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9142 q = 1) (hb : d93078 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9143 q = 1) (hb : d93079 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d93079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9143, d93079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9144 q = 1) (hb : d93080 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d93080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9144, d93080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9145 q = 1) (hb : d93081 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9145, d93081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9145, d93081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11522 (p : Pattern) (ha : d93087 p = 1) (hb : d93826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93082 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11521 q hb ha
    | true =>
      simp only [d93082, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d93083 q = 1) (hb : d93822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93083, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93083, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93084 q = 1) (hb : d93823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93084, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93084, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93085 q = 1) (hb : d93824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93085, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93085, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93086 q = 1) (hb : d93825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93086, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93086, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93087 q = 1) (hb : d93826 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93087, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93087, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11523 (p : Pattern) (ha : d9167 p = 1) (hb : d93090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d93076 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11520 q ha hb
    | true =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d93077 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9142 q = 1) (hb : d93078 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9143 q = 1) (hb : d93079 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d93079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9143, d93079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9144 q = 1) (hb : d93080 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d93080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9144, d93080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9167 q = 1) (hb : d93090 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9167, d93090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9167, d93090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11524 (p : Pattern) (ha : d93096 p = 1) (hb : d93834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93082 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11521 q hb ha
    | true =>
      simp only [d93082, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d93083 q = 1) (hb : d93822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93083, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93083, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93084 q = 1) (hb : d93823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93084, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93084, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93085 q = 1) (hb : d93824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93085, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93085, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93086 q = 1) (hb : d93825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93086, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93086, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93091 q = 1) (hb : d93829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93091, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11523 q hb ha
    | true =>
      simp only [d93091, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h7 (q : Pattern) (ha : d93092 q = 1) (hb : d93830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93092, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93092, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93093 q = 1) (hb : d93831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93093, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93093, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d93094 q = 1) (hb : d93832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93094, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93094, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93095 q = 1) (hb : d93833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93095, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93095, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93096 q = 1) (hb : d93834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93096, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93096, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro11525 (p : Pattern) (ha : d9145 p = 1) (hb : d93130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d93076 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11520 q ha hb
    | true =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d93077 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d93127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d93127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d93127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d93128 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d93128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d93128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9144 q = 1) (hb : d93129 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d93129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9144, d93129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9145 q = 1) (hb : d93130 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9145, d93130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9145, d93130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11526 (p : Pattern) (ha : d93101 p = 1) (hb : d93839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d93076 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11520 q ha hb
    | true =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d93077 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9142 q = 1) (hb : d93078 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9143 q = 1) (hb : d93079 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d93079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9143, d93079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d93100 q = 1) (hb : d93838 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93100, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93100, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93101 q = 1) (hb : d93839 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93101, d93839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93101, d93839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11527 (p : Pattern) (ha : d93108 p = 1) (hb : d93846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d93076 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11520 q ha hb
    | true =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d93077 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9142 q = 1) (hb : d93078 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93106 q = 1) (hb : d93844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93106, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93106, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93107 q = 1) (hb : d93845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93107, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93107, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93108 q = 1) (hb : d93846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93108, d93846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93108, d93846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11528 (p : Pattern) (ha : d9119 p = 1) (hb : d93114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2150 q = 1) (hb : d53429 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro290 q ha hb
    | true =>
      simp only [d2150, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
  have h2 (q : Pattern) (ha : d2151 q = 1) (hb : d53430 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2151, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2152 q = 1) (hb : d53431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2152, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9117 q = 1) (hb : d93112 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9117, d93112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9117, d93112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2073 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
  have h6 (q : Pattern) (ha : d2074 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2075 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7115 q = 1) (hb : d81903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d81903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7115, d81903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9118 q = 1) (hb : d93113 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9118, d93113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9118, d93113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9119 q = 1) (hb : d93114 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9119, d93114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9119, d93114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11529 (p : Pattern) (ha : d93120 p = 1) (hb : d93853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d93115 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d93115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11528 q ha hb
    | true =>
      simp only [d9120, d93115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d93116 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d93116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d93116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81907 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93117 q = 1) (hb : d93850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93117, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93117, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d93118 q = 1) (hb : d93851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93118, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93118, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93119 q = 1) (hb : d93852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93119, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93119, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93120 q = 1) (hb : d93853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93120, d93853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93120, d93853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11530 (p : Pattern) (ha : d7117 p = 1) (hb : d81905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7115 q = 1) (hb : d81903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d81903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d81903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5253 q = 1) (hb : d69337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d69337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7979 q ha hb
    | true =>
      simp only [d5253, d69337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7981 q ha hb
  have h6 (q : Pattern) (ha : d5254 q = 1) (hb : d69338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d69338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d69338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5255 q = 1) (hb : d69339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d69339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d69339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5256 q = 1) (hb : d69340 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d69340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5256, d69340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7116 q = 1) (hb : d81904 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7116, d81904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7116, d81904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7117 q = 1) (hb : d81905 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7117, d81905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7117, d81905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11531 (p : Pattern) (ha : d93124 p = 1) (hb : d93857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d81906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d81906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11530 q ha hb
    | true =>
      simp only [d7118, d81906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d81907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d81907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d81907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93121 q = 1) (hb : d93854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93121, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93121, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d93122 q = 1) (hb : d93855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93122, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93122, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93123 q = 1) (hb : d93856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93123, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93123, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93124 q = 1) (hb : d93857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93124, d93857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93124, d93857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11532 (p : Pattern) (ha : d93136 p = 1) (hb : d93863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93102 q = 1) (hb : d93840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93102, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11526 q ha hb
    | true =>
      simp only [d93102, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q hb ha
  have h2 (q : Pattern) (ha : d93103 q = 1) (hb : d93841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93103, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93103, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93104 q = 1) (hb : d93842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93104, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93104, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93105 q = 1) (hb : d93843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93105, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93105, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93109 q = 1) (hb : d93847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93109, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11527 q ha hb
    | true =>
      simp only [d93109, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q hb ha
  have h6 (q : Pattern) (ha : d93110 q = 1) (hb : d93848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93110, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93110, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93111 q = 1) (hb : d93849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93111, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93111, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93125 q = 1) (hb : d93858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93125, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11529 q ha hb
    | true =>
      simp only [d93125, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11531 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d93082 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d93126 q = 1) (hb : d93859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93126, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9146 q = 1) (hb : d93131 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d93131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11525 q ha hb
    | true =>
      simp only [d9146, d93131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9147 q = 1) (hb : d93132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d93132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9147, d93132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93133 q = 1) (hb : d93860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93133, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d93134 q = 1) (hb : d93861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93134, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93135 q = 1) (hb : d93862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93135, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93136 q = 1) (hb : d93863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93136, d93863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93136, d93863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro11533 (p : Pattern) (ha : d9167 p = 1) (hb : d93150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d93076 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11520 q ha hb
    | true =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d93077 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d93127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d93127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d93127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d93128 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d93128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d93128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9144 q = 1) (hb : d93129 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d93129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9144, d93129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9167 q = 1) (hb : d93150 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9167, d93150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9167, d93150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11534 (p : Pattern) (ha : d93137 p = 1) (hb : d93864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d93076 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11520 q ha hb
    | true =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d93077 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9142 q = 1) (hb : d93078 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9143 q = 1) (hb : d93079 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d93079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9143, d93079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d93100 q = 1) (hb : d93838 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93100, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93100, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93137 q = 1) (hb : d93864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93137, d93864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93137, d93864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11535 (p : Pattern) (ha : d93142 p = 1) (hb : d93869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d93076 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11520 q ha hb
    | true =>
      simp only [d9081, d93076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d93077 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d93077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9142 q = 1) (hb : d93078 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d93078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93106 q = 1) (hb : d93844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93106, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93106, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93107 q = 1) (hb : d93845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93107, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93107, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93142 q = 1) (hb : d93869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93142, d93869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93142, d93869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11536 (p : Pattern) (ha : d93146 p = 1) (hb : d93873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d93115 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d93115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11528 q ha hb
    | true =>
      simp only [d9120, d93115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d93116 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d93116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d93116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81907 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93117 q = 1) (hb : d93850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93117, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93117, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d93118 q = 1) (hb : d93851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93118, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93118, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93119 q = 1) (hb : d93852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93119, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93119, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93146 q = 1) (hb : d93873 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93146, d93873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93146, d93873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11537 (p : Pattern) (ha : d93147 p = 1) (hb : d93874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d81906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d81906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11530 q ha hb
    | true =>
      simp only [d7118, d81906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d81907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d81907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d81907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93121 q = 1) (hb : d93854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93121, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93121, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d93122 q = 1) (hb : d93855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93122, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93122, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93123 q = 1) (hb : d93856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93123, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93123, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93147 q = 1) (hb : d93874 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93147, d93874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93147, d93874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11538 (p : Pattern) (ha : d93156 p = 1) (hb : d93880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93102 q = 1) (hb : d93840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93102, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11526 q ha hb
    | true =>
      simp only [d93102, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q hb ha
  have h2 (q : Pattern) (ha : d93103 q = 1) (hb : d93841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93103, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93103, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93104 q = 1) (hb : d93842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93104, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93104, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93105 q = 1) (hb : d93843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93105, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93105, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93109 q = 1) (hb : d93847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93109, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11527 q ha hb
    | true =>
      simp only [d93109, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q hb ha
  have h6 (q : Pattern) (ha : d93110 q = 1) (hb : d93848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93110, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93110, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93111 q = 1) (hb : d93849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93111, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93111, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93125 q = 1) (hb : d93858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93125, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11529 q ha hb
    | true =>
      simp only [d93125, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11531 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d93082 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d93126 q = 1) (hb : d93859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93126, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9146 q = 1) (hb : d93131 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d93131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11525 q ha hb
    | true =>
      simp only [d9146, d93131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9147 q = 1) (hb : d93132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d93132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9147, d93132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93133 q = 1) (hb : d93860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93133, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d93134 q = 1) (hb : d93861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93134, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93135 q = 1) (hb : d93862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93135, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93138 q = 1) (hb : d93865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93138, d93865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11534 q ha hb
    | true =>
      simp only [d93138, d93865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro308 q hb ha
  have h17 (q : Pattern) (ha : d93139 q = 1) (hb : d93866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93139, d93866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93139, d93866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93140 q = 1) (hb : d93867 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93140, d93867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93140, d93867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d93141 q = 1) (hb : d93868 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93141, d93868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93141, d93868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d93143 q = 1) (hb : d93870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93143, d93870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11535 q ha hb
    | true =>
      simp only [d93143, d93870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q hb ha
  have h21 (q : Pattern) (ha : d93144 q = 1) (hb : d93871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93144, d93871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93144, d93871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d93145 q = 1) (hb : d93872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93145, d93872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d93145, d93872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d93148 q = 1) (hb : d93875 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93148, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11536 q ha hb
    | true =>
      simp only [d93148, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11537 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d93091 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d93149 q = 1) (hb : d93876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d93149, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d9168 q = 1) (hb : d93151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d93151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11533 q ha hb
    | true =>
      simp only [d9168, d93151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d9169 q = 1) (hb : d93152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d93152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9169, d93152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d93153 q = 1) (hb : d93877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d93153, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d93154 q = 1) (hb : d93878 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93154, d93878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d93154, d93878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d93155 q = 1) (hb : d93879 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93155, d93879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93155, d93879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d93156 q = 1) (hb : d93880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93156, d93880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93156, d93880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro11539 (p : Pattern) (ha : d93163 p = 1) (hb : d93887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93158 q = 1) (hb : d93882 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93158, d93882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11531 q ha hb
    | true =>
      simp only [d93158, d93882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d93159 q = 1) (hb : d93883 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93159, d93883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93159, d93883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93160 q = 1) (hb : d93884 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93160, d93884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93160, d93884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93161 q = 1) (hb : d93885 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93161, d93885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93161, d93885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93162 q = 1) (hb : d93886 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93162, d93886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93162, d93886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d93163 q = 1) (hb : d93887 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93163, d93887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93163, d93887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro11540 (p : Pattern) (ha : d93170 p = 1) (hb : d93894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93148 q = 1) (hb : d93875 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93148, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11536 q ha hb
    | true =>
      simp only [d93148, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11537 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93149 q = 1) (hb : d93876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93149, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9168 q = 1) (hb : d93151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d93151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11533 q ha hb
    | true =>
      simp only [d9168, d93151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9169 q = 1) (hb : d93152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d93152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9169, d93152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d93153 q = 1) (hb : d93877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93153, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93168 q = 1) (hb : d93892 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93168, d93892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93168, d93892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93169 q = 1) (hb : d93893 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93169, d93893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93169, d93893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93170 q = 1) (hb : d93894 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93170, d93894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93170, d93894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11541 (p : Pattern) (ha : d9219 p = 1) (hb : d93191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7161 q = 1) (hb : d81949 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d81949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d81949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2367 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro285 q ha hb
  have h6 (q : Pattern) (ha : d2368 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2369 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2375 q = 1) (hb : d53540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2375, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9218 q = 1) (hb : d93190 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9218, d93190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9218, d93190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9219 q = 1) (hb : d93191 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9219, d93191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9219, d93191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11542 (p : Pattern) (ha : d9225 p = 1) (hb : d93203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d93192 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d93192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11541 q ha hb
    | true =>
      simp only [d9220, d93192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d93193 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d93193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d93193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9222 q = 1) (hb : d93200 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9222, d93200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9222, d93200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9223 q = 1) (hb : d93201 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9223, d93201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9223, d93201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9224 q = 1) (hb : d93202 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9224, d93202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9224, d93202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9225 q = 1) (hb : d93203 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9225, d93203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9225, d93203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11543 (p : Pattern) (ha : d9195 p = 1) (hb : d93178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2352 q = 1) (hb : d53517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro294 q ha hb
    | true =>
      simp only [d2352, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
  have h2 (q : Pattern) (ha : d2353 q = 1) (hb : d53518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2354 q = 1) (hb : d53519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9193 q = 1) (hb : d93176 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9193, d93176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9193, d93176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2357 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
  have h6 (q : Pattern) (ha : d2358 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2359 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7161 q = 1) (hb : d81949 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d81949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7161, d81949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9194 q = 1) (hb : d93177 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9194, d93177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9194, d93177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9195 q = 1) (hb : d93178 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9195, d93178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9195, d93178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11544 (p : Pattern) (ha : d93184 p = 1) (hb : d93903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9196 q = 1) (hb : d93179 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9196, d93179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11543 q ha hb
    | true =>
      simp only [d9196, d93179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9197 q = 1) (hb : d93180 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9197, d93180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9197, d93180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81953 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93181 q = 1) (hb : d93900 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93181, d93900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93181, d93900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d93182 q = 1) (hb : d93901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93182, d93901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93182, d93901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93183 q = 1) (hb : d93902 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93183, d93902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93183, d93902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93184 q = 1) (hb : d93903 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93184, d93903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93184, d93903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11545 (p : Pattern) (ha : d7163 p = 1) (hb : d81951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7161 q = 1) (hb : d81949 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d81949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d81949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6649 q = 1) (hb : d76367 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d76367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10914 q ha hb
    | true =>
      simp only [d6649, d76367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10915 q ha hb
  have h6 (q : Pattern) (ha : d6650 q = 1) (hb : d76368 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d76368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d76368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6651 q = 1) (hb : d76369 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d76369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d76369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6652 q = 1) (hb : d76370 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d76370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6652, d76370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7162 q = 1) (hb : d81950 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7162, d81950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7162, d81950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7163 q = 1) (hb : d81951 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7163, d81951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7163, d81951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11546 (p : Pattern) (ha : d93188 p = 1) (hb : d93907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7164 q = 1) (hb : d81952 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d81952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11545 q ha hb
    | true =>
      simp only [d7164, d81952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7165 q = 1) (hb : d81953 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d81953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d81953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93185 q = 1) (hb : d93904 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93185, d93904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93185, d93904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d93186 q = 1) (hb : d93905 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93186, d93905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93186, d93905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93187 q = 1) (hb : d93906 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93187, d93906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93187, d93906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93188 q = 1) (hb : d93907 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93188, d93907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93188, d93907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11547 (p : Pattern) (ha : d93209 p = 1) (hb : d93913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93189 q = 1) (hb : d93908 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93189, d93908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11544 q ha hb
    | true =>
      simp only [d93189, d93908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11546 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93199 q = 1) (hb : d93909 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93199, d93909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93199, d93909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9226 q = 1) (hb : d93204 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9226, d93204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11542 q ha hb
    | true =>
      simp only [d9226, d93204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9227 q = 1) (hb : d93205 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9227, d93205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9227, d93205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d93206 q = 1) (hb : d93910 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93206, d93910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93206, d93910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93207 q = 1) (hb : d93911 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93207, d93911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93207, d93911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93208 q = 1) (hb : d93912 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93208, d93912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93208, d93912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93209 q = 1) (hb : d93913 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93209, d93913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93209, d93913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11548 (p : Pattern) (ha : d93215 p = 1) (hb : d93919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93088 q = 1) (hb : d93827 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93088, d93827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93088, d93827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11522 q ha hb
  have h2 (q : Pattern) (ha : d93089 q = 1) (hb : d93828 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93089, d93828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93089, d93828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93097 q = 1) (hb : d93835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93097, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11522 q ha hb
    | true =>
      simp only [d93097, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11524 q ha hb
  have h4 (q : Pattern) (ha : d93098 q = 1) (hb : d93836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93098, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93098, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93099 q = 1) (hb : d93837 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93099, d93837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93099, d93837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93157 q = 1) (hb : d93881 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93157, d93881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11532 q ha hb
    | true =>
      simp only [d93157, d93881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11538 q ha hb
  have h7 (q : Pattern) (ha : d93164 q = 1) (hb : d93888 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93164, d93888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11539 q ha hb
    | true =>
      simp only [d93164, d93888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q hb ha
  have h8 (q : Pattern) (ha : d93165 q = 1) (hb : d93889 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93165, d93889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93165, d93889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93166 q = 1) (hb : d93890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93166, d93890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93166, d93890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d93167 q = 1) (hb : d93891 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93167, d93891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93167, d93891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93171 q = 1) (hb : d93895 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93171, d93895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93171, d93895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11540 q ha hb
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
  have h13 (q : Pattern) (ha : d93172 q = 1) (hb : d93896 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93172, d93896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93172, d93896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d93173 q = 1) (hb : d93897 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93173, d93897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93173, d93897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d93174 q = 1) (hb : d93898 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93174, d93898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d93174, d93898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d93175 q = 1) (hb : d93899 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93175, d93899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93175, d93899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93210 q = 1) (hb : d93914 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93210, d93914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93210, d93914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11547 q ha hb
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
  have h19 (q : Pattern) (ha : d93211 q = 1) (hb : d93915 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93211, d93915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93211, d93915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d93212 q = 1) (hb : d93916 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93212, d93916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93212, d93916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d93213 q = 1) (hb : d93917 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93213, d93917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d93213, d93917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d93214 q = 1) (hb : d93918 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93214, d93918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d93214, d93918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d93215 q = 1) (hb : d93919 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93215, d93919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93215, d93919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11549 (p : Pattern) (ha : d93221 p = 1) (hb : d93925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93216 q = 1) (hb : d93920 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93216, d93920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93216, d93920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11548 q ha hb
  have h2 (q : Pattern) (ha : d93217 q = 1) (hb : d93921 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93217, d93921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93217, d93921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93218 q = 1) (hb : d93922 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93218, d93922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93218, d93922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93219 q = 1) (hb : d93923 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93219, d93923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93219, d93923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93220 q = 1) (hb : d93924 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93220, d93924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93220, d93924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93221 q = 1) (hb : d93925 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93221, d93925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93221, d93925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11550 (p : Pattern) (ha : d93227 p = 1) (hb : d93931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d92620 q = 1) (hb : d93496 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92620, d93496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11401 q ha hb
    | true =>
      simp only [d92620, d93496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11429 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92769 q = 1) (hb : d93602 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92769, d93602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92769, d93602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11459 q ha hb
  have h3 (q : Pattern) (ha : d92770 q = 1) (hb : d93603 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92770, d93603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d92770, d93603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92919 q = 1) (hb : d93709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92919, d93709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92919, d93709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11489 q ha hb
  have h5 (q : Pattern) (ha : d92920 q = 1) (hb : d93710 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92920, d93710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92920, d93710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92921 q = 1) (hb : d93711 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d92921, d93711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92921, d93711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93070 q = 1) (hb : d93817 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93070, d93817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93070, d93817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11519 q ha hb
  have h8 (q : Pattern) (ha : d93071 q = 1) (hb : d93818 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93071, d93818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93071, d93818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93072 q = 1) (hb : d93819 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93072, d93819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93072, d93819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93073 q = 1) (hb : d93820 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93073, d93820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93073, d93820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93222 q = 1) (hb : d93926 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93222, d93926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93222, d93926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11549 q ha hb
  have h12 (q : Pattern) (ha : d93223 q = 1) (hb : d93927 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93223, d93927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93223, d93927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93224 q = 1) (hb : d93928 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93224, d93928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93224, d93928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93225 q = 1) (hb : d93929 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93225, d93929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93225, d93929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93226 q = 1) (hb : d93930 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d93226, d93930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93226, d93930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93227 q = 1) (hb : d93931 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d93227, d93931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93227, d93931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro11551 (p : Pattern) (ha : d93233 p = 1) (hb : d93937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93228 q = 1) (hb : d93932 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d93228, d93932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11550 q ha hb
    | true =>
      simp only [d93228, d93932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93229 q = 1) (hb : d93933 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d93229, d93933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93229, d93933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93230 q = 1) (hb : d93934 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d93230, d93934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93230, d93934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93231 q = 1) (hb : d93935 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d93231, d93935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93231, d93935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93232 q = 1) (hb : d93936 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d93232, d93936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93232, d93936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93233 q = 1) (hb : d93937 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d93233, d93937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93233, d93937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11552 (p : Pattern) (ha : d93239 p = 1) (hb : d93943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93234 q = 1) (hb : d93938 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d93234, d93938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11551 q ha hb
    | true =>
      simp only [d93234, d93938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93235 q = 1) (hb : d93939 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d93235, d93939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93235, d93939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93236 q = 1) (hb : d93940 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d93236, d93940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93236, d93940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93237 q = 1) (hb : d93941 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d93237, d93941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93237, d93941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93238 q = 1) (hb : d93942 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d93238, d93942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93238, d93942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93239 q = 1) (hb : d93943 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d93239, d93943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93239, d93943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11553 (p : Pattern) (ha : d93245 p = 1) (hb : d93949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93240 q = 1) (hb : d93944 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d93240, d93944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11552 q ha hb
    | true =>
      simp only [d93240, d93944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93241 q = 1) (hb : d93945 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d93241, d93945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93241, d93945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93242 q = 1) (hb : d93946 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d93242, d93946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93242, d93946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93243 q = 1) (hb : d93947 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d93243, d93947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93243, d93947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93244 q = 1) (hb : d93948 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d93244, d93948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93244, d93948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93245 q = 1) (hb : d93949 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d93245, d93949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93245, d93949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11554 (p : Pattern) (ha : d93251 p = 1) (hb : d93955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93246 q = 1) (hb : d93950 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d93246, d93950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11553 q ha hb
    | true =>
      simp only [d93246, d93950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93247 q = 1) (hb : d93951 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d93247, d93951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93247, d93951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93248 q = 1) (hb : d93952 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d93248, d93952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93248, d93952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93249 q = 1) (hb : d93953 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d93249, d93953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93249, d93953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93250 q = 1) (hb : d93954 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d93250, d93954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93250, d93954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93251 q = 1) (hb : d93955 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d93251, d93955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93251, d93955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11555 (p : Pattern) (ha : d93257 p = 1) (hb : d93961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93252 q = 1) (hb : d93956 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d93252, d93956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11554 q ha hb
    | true =>
      simp only [d93252, d93956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93253 q = 1) (hb : d93957 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d93253, d93957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93253, d93957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93254 q = 1) (hb : d93958 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d93254, d93958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93254, d93958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93255 q = 1) (hb : d93959 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d93255, d93959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93255, d93959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93256 q = 1) (hb : d93960 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d93256, d93960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93256, d93960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93257 q = 1) (hb : d93961 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d93257, d93961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93257, d93961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11556 (p : Pattern) (ha : d93263 p = 1) (hb : d93967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93258 q = 1) (hb : d93962 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d93258, d93962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11555 q ha hb
    | true =>
      simp only [d93258, d93962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93259 q = 1) (hb : d93963 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d93259, d93963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93259, d93963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93260 q = 1) (hb : d93964 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d93260, d93964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93260, d93964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93261 q = 1) (hb : d93965 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d93261, d93965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93261, d93965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93262 q = 1) (hb : d93966 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d93262, d93966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93262, d93966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93263 q = 1) (hb : d93967 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d93263, d93967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93263, d93967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11557 (p : Pattern) (ha : d93269 p = 1) (hb : d93973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93264 q = 1) (hb : d93968 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d93264, d93968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11556 q ha hb
    | true =>
      simp only [d93264, d93968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93265 q = 1) (hb : d93969 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d93265, d93969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93265, d93969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93266 q = 1) (hb : d93970 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d93266, d93970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93266, d93970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93267 q = 1) (hb : d93971 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d93267, d93971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93267, d93971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93268 q = 1) (hb : d93972 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d93268, d93972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93268, d93972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93269 q = 1) (hb : d93973 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d93269, d93973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93269, d93973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11558 (p : Pattern) (ha : d82697 p = 1) (hb : d92314 p = 1) : d93976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d92314 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5856 q = 1) (hb : d92314 q = 1) : d93276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11198 q ha hb
    | true =>
      simp only [d5856, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5898 q = 1) (hb : d92314 q = 1) : d93318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5898, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5899 q = 1) (hb : d92314 q = 1) : d93319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5899, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5900 q = 1) (hb : d92314 q = 1) : d93320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5901 q = 1) (hb : d92314 q = 1) : d93321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82697 q = 1) (hb : d92314 q = 1) : d93976 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82697, d93976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82697, d93976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11559 (p : Pattern) (ha : d82707 p = 1) (hb : d92314 p = 1) : d93986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d92314 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5874 q = 1) (hb : d92314 q = 1) : d93294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5874, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11202 q ha hb
    | true =>
      simp only [d5874, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82703 q = 1) (hb : d92314 q = 1) : d93982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82703, d93982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82703, d93982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82704 q = 1) (hb : d92314 q = 1) : d93983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82704, d93983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82704, d93983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82705 q = 1) (hb : d92314 q = 1) : d93984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82705, d93984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82705, d93984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82706 q = 1) (hb : d92314 q = 1) : d93985 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82706, d93985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82706, d93985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82707 q = 1) (hb : d92314 q = 1) : d93986 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82707, d93986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82707, d93986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11560 (p : Pattern) (ha : d82713 p = 1) (hb : d92314 p = 1) : d93992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5903 q = 1) (hb : d92314 q = 1) : d93323 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11205 q ha hb
    | true =>
      simp only [d5903, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11206 q ha hb
  have h2 (q : Pattern) (ha : d5904 q = 1) (hb : d92314 q = 1) : d93324 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5904, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82695 q = 1) (hb : d92314 q = 1) : d93974 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82695, d93974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82695, d93974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82696 q = 1) (hb : d92314 q = 1) : d93975 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82696, d93975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82696, d93975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82698 q = 1) (hb : d92314 q = 1) : d93977 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82698, d93977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82698, d93977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11558 q ha hb
  have h6 (q : Pattern) (ha : d82699 q = 1) (hb : d92314 q = 1) : d93978 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82699, d93978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82699, d93978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82700 q = 1) (hb : d92314 q = 1) : d93979 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82700, d93979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82700, d93979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82701 q = 1) (hb : d92314 q = 1) : d93980 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82701, d93980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82701, d93980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82702 q = 1) (hb : d92314 q = 1) : d93981 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82702, d93981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82702, d93981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82708 q = 1) (hb : d92314 q = 1) : d93987 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82708, d93987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82708, d93987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11559 q ha hb
  have h11 (q : Pattern) (ha : d82709 q = 1) (hb : d92314 q = 1) : d93988 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82709, d93988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82709, d93988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82710 q = 1) (hb : d92314 q = 1) : d93989 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82710, d93989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82710, d93989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82711 q = 1) (hb : d92314 q = 1) : d93990 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82711, d93990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82711, d93990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82712 q = 1) (hb : d92314 q = 1) : d93991 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82712, d93991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82712, d93991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82713 q = 1) (hb : d92314 q = 1) : d93992 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82713, d93992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82713, d93992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11561 (p : Pattern) (ha : d82719 p = 1) (hb : d92314 p = 1) : d93998 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d92314 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82714 q = 1) (hb : d92314 q = 1) : d93993 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82714, d93993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82714, d93993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11560 q ha hb
  have h3 (q : Pattern) (ha : d82715 q = 1) (hb : d92314 q = 1) : d93994 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82715, d93994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82715, d93994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82716 q = 1) (hb : d92314 q = 1) : d93995 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82716, d93995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82716, d93995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82717 q = 1) (hb : d92314 q = 1) : d93996 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82717, d93996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82717, d93996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82718 q = 1) (hb : d92314 q = 1) : d93997 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82718, d93997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82718, d93997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82719 q = 1) (hb : d92314 q = 1) : d93998 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82719, d93998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82719, d93998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11562 (p : Pattern) (ha : d82722 p = 1) (hb : d92314 p = 1) : d94001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d501 q = 1) (hb : d92314 q = 1) : d501 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6000 q = 1) (hb : d92314 q = 1) : d93399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6000, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11226 q ha hb
    | true =>
      simp only [d6000, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6001 q = 1) (hb : d92314 q = 1) : d93400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6001, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6002 q = 1) (hb : d92314 q = 1) : d93401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6002, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6003 q = 1) (hb : d92314 q = 1) : d93402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6004 q = 1) (hb : d92314 q = 1) : d93403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82722 q = 1) (hb : d92314 q = 1) : d94001 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82722, d94001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82722, d94001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11563 (p : Pattern) (ha : d82733 p = 1) (hb : d92314 p = 1) : d94012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d730 q = 1) (hb : d92314 q = 1) : d730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82728 q = 1) (hb : d92314 q = 1) : d94007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d82728, d94007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11243 q ha hb
    | true =>
      simp only [d82728, d94007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82729 q = 1) (hb : d92314 q = 1) : d94008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82729, d94008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82729, d94008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82730 q = 1) (hb : d92314 q = 1) : d94009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82730, d94009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82730, d94009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82731 q = 1) (hb : d92314 q = 1) : d94010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82731, d94010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82731, d94010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82732 q = 1) (hb : d92314 q = 1) : d94011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82732, d94011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82732, d94011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82733 q = 1) (hb : d92314 q = 1) : d94012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82733, d94012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82733, d94012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11564 (p : Pattern) (ha : d82739 p = 1) (hb : d92314 p = 1) : d94018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6006 q = 1) (hb : d92314 q = 1) : d93405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11225 q ha hb
    | true =>
      simp only [d6006, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11227 q ha hb
  have h2 (q : Pattern) (ha : d6007 q = 1) (hb : d92314 q = 1) : d93406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6007, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82720 q = 1) (hb : d92314 q = 1) : d93999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82720, d93999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82720, d93999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82721 q = 1) (hb : d92314 q = 1) : d94000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82721, d94000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82721, d94000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82723 q = 1) (hb : d92314 q = 1) : d94002 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82723, d94002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82723, d94002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11562 q ha hb
  have h6 (q : Pattern) (ha : d82724 q = 1) (hb : d92314 q = 1) : d94003 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82724, d94003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82724, d94003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82725 q = 1) (hb : d92314 q = 1) : d94004 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82725, d94004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82725, d94004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82726 q = 1) (hb : d92314 q = 1) : d94005 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82726, d94005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82726, d94005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82727 q = 1) (hb : d92314 q = 1) : d94006 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82727, d94006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82727, d94006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82734 q = 1) (hb : d92314 q = 1) : d94013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82734, d94013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82734, d94013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11563 q ha hb
  have h11 (q : Pattern) (ha : d82735 q = 1) (hb : d92314 q = 1) : d94014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82735, d94014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82735, d94014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82736 q = 1) (hb : d92314 q = 1) : d94015 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82736, d94015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82736, d94015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82737 q = 1) (hb : d92314 q = 1) : d94016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82737, d94016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82737, d94016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82738 q = 1) (hb : d92314 q = 1) : d94017 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82738, d94017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82738, d94017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82739 q = 1) (hb : d92314 q = 1) : d94018 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82739, d94018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82739, d94018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11565 (p : Pattern) (ha : d82745 p = 1) (hb : d92314 p = 1) : d94024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82740 q = 1) (hb : d92314 q = 1) : d94019 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82740, d94019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82740, d94019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11564 q ha hb
  have h2 (q : Pattern) (ha : d82741 q = 1) (hb : d92314 q = 1) : d94020 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82741, d94020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82741, d94020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82742 q = 1) (hb : d92314 q = 1) : d94021 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82742, d94021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82742, d94021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82743 q = 1) (hb : d92314 q = 1) : d94022 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82743, d94022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82743, d94022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82744 q = 1) (hb : d92314 q = 1) : d94023 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82744, d94023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82744, d94023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82745 q = 1) (hb : d92314 q = 1) : d94024 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82745, d94024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82745, d94024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11566 (p : Pattern) (ha : d82749 p = 1) (hb : d92314 p = 1) : d94028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d793 q = 1) (hb : d92314 q = 1) : d793 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6128 q = 1) (hb : d92314 q = 1) : d93505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6128, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11254 q ha hb
    | true =>
      simp only [d6128, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6129 q = 1) (hb : d92314 q = 1) : d93506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6129, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6130 q = 1) (hb : d92314 q = 1) : d93507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6130, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6131 q = 1) (hb : d92314 q = 1) : d93508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6132 q = 1) (hb : d92314 q = 1) : d93509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82749 q = 1) (hb : d92314 q = 1) : d94028 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82749, d94028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82749, d94028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11567 (p : Pattern) (ha : d82760 p = 1) (hb : d92314 p = 1) : d94039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1063 q = 1) (hb : d92314 q = 1) : d1063 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82755 q = 1) (hb : d92314 q = 1) : d94034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d82755, d94034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11275 q ha hb
    | true =>
      simp only [d82755, d94034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82756 q = 1) (hb : d92314 q = 1) : d94035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82756, d94035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82756, d94035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82757 q = 1) (hb : d92314 q = 1) : d94036 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82757, d94036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82757, d94036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82758 q = 1) (hb : d92314 q = 1) : d94037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82758, d94037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82758, d94037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82759 q = 1) (hb : d92314 q = 1) : d94038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82759, d94038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82759, d94038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82760 q = 1) (hb : d92314 q = 1) : d94039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82760, d94039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82760, d94039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11568 (p : Pattern) (ha : d82766 p = 1) (hb : d92314 p = 1) : d94045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6134 q = 1) (hb : d92314 q = 1) : d93511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11253 q ha hb
    | true =>
      simp only [d6134, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11255 q ha hb
  have h2 (q : Pattern) (ha : d6135 q = 1) (hb : d92314 q = 1) : d93512 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6135, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82747 q = 1) (hb : d92314 q = 1) : d94026 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82747, d94026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82747, d94026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82748 q = 1) (hb : d92314 q = 1) : d94027 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82748, d94027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82748, d94027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82750 q = 1) (hb : d92314 q = 1) : d94029 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82750, d94029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82750, d94029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11566 q ha hb
  have h6 (q : Pattern) (ha : d82751 q = 1) (hb : d92314 q = 1) : d94030 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82751, d94030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82751, d94030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82752 q = 1) (hb : d92314 q = 1) : d94031 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82752, d94031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82752, d94031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82753 q = 1) (hb : d92314 q = 1) : d94032 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82753, d94032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82753, d94032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82754 q = 1) (hb : d92314 q = 1) : d94033 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82754, d94033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82754, d94033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82761 q = 1) (hb : d92314 q = 1) : d94040 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82761, d94040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82761, d94040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11567 q ha hb
  have h11 (q : Pattern) (ha : d82762 q = 1) (hb : d92314 q = 1) : d94041 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82762, d94041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82762, d94041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82763 q = 1) (hb : d92314 q = 1) : d94042 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82763, d94042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82763, d94042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82764 q = 1) (hb : d92314 q = 1) : d94043 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82764, d94043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82764, d94043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82765 q = 1) (hb : d92314 q = 1) : d94044 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82765, d94044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82765, d94044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82766 q = 1) (hb : d92314 q = 1) : d94045 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82766, d94045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82766, d94045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11569 (p : Pattern) (ha : d82772 p = 1) (hb : d92314 p = 1) : d94051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82767 q = 1) (hb : d92314 q = 1) : d94046 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82767, d94046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82767, d94046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11568 q ha hb
  have h2 (q : Pattern) (ha : d82768 q = 1) (hb : d92314 q = 1) : d94047 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82768, d94047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82768, d94047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82769 q = 1) (hb : d92314 q = 1) : d94048 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82769, d94048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82769, d94048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82770 q = 1) (hb : d92314 q = 1) : d94049 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82770, d94049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82770, d94049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82771 q = 1) (hb : d92314 q = 1) : d94050 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82771, d94050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82771, d94050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82772 q = 1) (hb : d92314 q = 1) : d94051 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82772, d94051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82772, d94051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11570 (p : Pattern) (ha : d82777 p = 1) (hb : d92314 p = 1) : d94056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1172 q = 1) (hb : d92314 q = 1) : d1172 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6267 q = 1) (hb : d92314 q = 1) : d93612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6267, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11282 q ha hb
    | true =>
      simp only [d6267, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6268 q = 1) (hb : d92314 q = 1) : d93613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6268, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6269 q = 1) (hb : d92314 q = 1) : d93614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6269, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6270 q = 1) (hb : d92314 q = 1) : d93615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6271 q = 1) (hb : d92314 q = 1) : d93616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82777 q = 1) (hb : d92314 q = 1) : d94056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82777, d94056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82777, d94056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11571 (p : Pattern) (ha : d82788 p = 1) (hb : d92314 p = 1) : d94067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1497 q = 1) (hb : d92314 q = 1) : d1497 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82783 q = 1) (hb : d92314 q = 1) : d94062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d82783, d94062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11303 q ha hb
    | true =>
      simp only [d82783, d94062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82784 q = 1) (hb : d92314 q = 1) : d94063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82784, d94063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82784, d94063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82785 q = 1) (hb : d92314 q = 1) : d94064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82785, d94064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82785, d94064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82786 q = 1) (hb : d92314 q = 1) : d94065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82786, d94065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82786, d94065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82787 q = 1) (hb : d92314 q = 1) : d94066 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82787, d94066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82787, d94066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82788 q = 1) (hb : d92314 q = 1) : d94067 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82788, d94067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82788, d94067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11572 (p : Pattern) (ha : d82794 p = 1) (hb : d92314 p = 1) : d94073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6273 q = 1) (hb : d92314 q = 1) : d93618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11281 q ha hb
    | true =>
      simp only [d6273, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11283 q ha hb
  have h2 (q : Pattern) (ha : d6274 q = 1) (hb : d92314 q = 1) : d93619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6274, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82775 q = 1) (hb : d92314 q = 1) : d94054 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82775, d94054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82775, d94054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82776 q = 1) (hb : d92314 q = 1) : d94055 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82776, d94055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82776, d94055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82778 q = 1) (hb : d92314 q = 1) : d94057 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82778, d94057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82778, d94057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11570 q ha hb
  have h6 (q : Pattern) (ha : d82779 q = 1) (hb : d92314 q = 1) : d94058 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82779, d94058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82779, d94058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82780 q = 1) (hb : d92314 q = 1) : d94059 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82780, d94059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82780, d94059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82781 q = 1) (hb : d92314 q = 1) : d94060 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82781, d94060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82781, d94060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82782 q = 1) (hb : d92314 q = 1) : d94061 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82782, d94061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82782, d94061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82789 q = 1) (hb : d92314 q = 1) : d94068 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82789, d94068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82789, d94068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11571 q ha hb
  have h11 (q : Pattern) (ha : d82790 q = 1) (hb : d92314 q = 1) : d94069 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82790, d94069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82790, d94069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82791 q = 1) (hb : d92314 q = 1) : d94070 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82791, d94070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82791, d94070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82792 q = 1) (hb : d92314 q = 1) : d94071 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82792, d94071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82792, d94071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82793 q = 1) (hb : d92314 q = 1) : d94072 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82793, d94072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82793, d94072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82794 q = 1) (hb : d92314 q = 1) : d94073 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82794, d94073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82794, d94073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11573 (p : Pattern) (ha : d82800 p = 1) (hb : d92314 p = 1) : d94079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82795 q = 1) (hb : d92314 q = 1) : d94074 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82795, d94074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82795, d94074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11572 q ha hb
  have h2 (q : Pattern) (ha : d82796 q = 1) (hb : d92314 q = 1) : d94075 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82796, d94075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82796, d94075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82797 q = 1) (hb : d92314 q = 1) : d94076 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82797, d94076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82797, d94076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82798 q = 1) (hb : d92314 q = 1) : d94077 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82798, d94077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82798, d94077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82799 q = 1) (hb : d92314 q = 1) : d94078 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82799, d94078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82799, d94078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82800 q = 1) (hb : d92314 q = 1) : d94079 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82800, d94079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82800, d94079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11574 (p : Pattern) (ha : d82806 p = 1) (hb : d92314 p = 1) : d94085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1633 q = 1) (hb : d92314 q = 1) : d1633 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6413 q = 1) (hb : d92314 q = 1) : d93720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6413, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11310 q ha hb
    | true =>
      simp only [d6413, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6414 q = 1) (hb : d92314 q = 1) : d93721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6414, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6415 q = 1) (hb : d92314 q = 1) : d93722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6415, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6416 q = 1) (hb : d92314 q = 1) : d93723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6417 q = 1) (hb : d92314 q = 1) : d93724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82806 q = 1) (hb : d92314 q = 1) : d94085 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82806, d94085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82806, d94085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11575 (p : Pattern) (ha : d82817 p = 1) (hb : d92314 p = 1) : d94096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1974 q = 1) (hb : d92314 q = 1) : d1974 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82812 q = 1) (hb : d92314 q = 1) : d94091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d82812, d94091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11331 q ha hb
    | true =>
      simp only [d82812, d94091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82813 q = 1) (hb : d92314 q = 1) : d94092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82813, d94092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82813, d94092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82814 q = 1) (hb : d92314 q = 1) : d94093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82814, d94093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82814, d94093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82815 q = 1) (hb : d92314 q = 1) : d94094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82815, d94094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82815, d94094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82816 q = 1) (hb : d92314 q = 1) : d94095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82816, d94095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82816, d94095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82817 q = 1) (hb : d92314 q = 1) : d94096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82817, d94096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82817, d94096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11576 (p : Pattern) (ha : d82823 p = 1) (hb : d92314 p = 1) : d94102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6419 q = 1) (hb : d92314 q = 1) : d93726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11309 q ha hb
    | true =>
      simp only [d6419, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11311 q ha hb
  have h2 (q : Pattern) (ha : d6420 q = 1) (hb : d92314 q = 1) : d93727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6420, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82804 q = 1) (hb : d92314 q = 1) : d94083 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82804, d94083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82804, d94083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82805 q = 1) (hb : d92314 q = 1) : d94084 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82805, d94084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82805, d94084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82807 q = 1) (hb : d92314 q = 1) : d94086 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82807, d94086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82807, d94086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11574 q ha hb
  have h6 (q : Pattern) (ha : d82808 q = 1) (hb : d92314 q = 1) : d94087 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82808, d94087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82808, d94087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82809 q = 1) (hb : d92314 q = 1) : d94088 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82809, d94088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82809, d94088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82810 q = 1) (hb : d92314 q = 1) : d94089 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82810, d94089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82810, d94089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82811 q = 1) (hb : d92314 q = 1) : d94090 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82811, d94090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82811, d94090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82818 q = 1) (hb : d92314 q = 1) : d94097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82818, d94097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82818, d94097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11575 q ha hb
  have h11 (q : Pattern) (ha : d82819 q = 1) (hb : d92314 q = 1) : d94098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82819, d94098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82819, d94098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82820 q = 1) (hb : d92314 q = 1) : d94099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82820, d94099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82820, d94099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82821 q = 1) (hb : d92314 q = 1) : d94100 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82821, d94100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82821, d94100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82822 q = 1) (hb : d92314 q = 1) : d94101 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82822, d94101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82822, d94101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82823 q = 1) (hb : d92314 q = 1) : d94102 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82823, d94102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82823, d94102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11577 (p : Pattern) (ha : d82829 p = 1) (hb : d92314 p = 1) : d94108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82824 q = 1) (hb : d92314 q = 1) : d94103 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82824, d94103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82824, d94103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11576 q ha hb
  have h2 (q : Pattern) (ha : d82825 q = 1) (hb : d92314 q = 1) : d94104 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82825, d94104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82825, d94104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82826 q = 1) (hb : d92314 q = 1) : d94105 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82826, d94105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82826, d94105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82827 q = 1) (hb : d92314 q = 1) : d94106 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82827, d94106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82827, d94106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82828 q = 1) (hb : d92314 q = 1) : d94107 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82828, d94107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82828, d94107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82829 q = 1) (hb : d92314 q = 1) : d94108 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82829, d94108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82829, d94108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11578 (p : Pattern) (ha : d82836 p = 1) (hb : d92314 p = 1) : d94115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2116 q = 1) (hb : d92314 q = 1) : d2116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6560 q = 1) (hb : d92314 q = 1) : d93829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6560, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11338 q ha hb
    | true =>
      simp only [d6560, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6561 q = 1) (hb : d92314 q = 1) : d93830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6561, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6562 q = 1) (hb : d92314 q = 1) : d93831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6562, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6563 q = 1) (hb : d92314 q = 1) : d93832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6564 q = 1) (hb : d92314 q = 1) : d93833 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82836 q = 1) (hb : d92314 q = 1) : d94115 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82836, d94115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82836, d94115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11579 (p : Pattern) (ha : d82847 p = 1) (hb : d92314 p = 1) : d94126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2452 q = 1) (hb : d92314 q = 1) : d2452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82842 q = 1) (hb : d92314 q = 1) : d94121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d82842, d94121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11359 q ha hb
    | true =>
      simp only [d82842, d94121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82843 q = 1) (hb : d92314 q = 1) : d94122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82843, d94122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82843, d94122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82844 q = 1) (hb : d92314 q = 1) : d94123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82844, d94123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82844, d94123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82845 q = 1) (hb : d92314 q = 1) : d94124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82845, d94124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82845, d94124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82846 q = 1) (hb : d92314 q = 1) : d94125 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82846, d94125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82846, d94125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82847 q = 1) (hb : d92314 q = 1) : d94126 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82847, d94126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82847, d94126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11580 (p : Pattern) (ha : d82853 p = 1) (hb : d92314 p = 1) : d94132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6566 q = 1) (hb : d92314 q = 1) : d93835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11337 q ha hb
    | true =>
      simp only [d6566, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11339 q ha hb
  have h2 (q : Pattern) (ha : d6567 q = 1) (hb : d92314 q = 1) : d93836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6567, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82834 q = 1) (hb : d92314 q = 1) : d94113 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82834, d94113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82834, d94113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82835 q = 1) (hb : d92314 q = 1) : d94114 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82835, d94114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82835, d94114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82837 q = 1) (hb : d92314 q = 1) : d94116 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82837, d94116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82837, d94116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11578 q ha hb
  have h6 (q : Pattern) (ha : d82838 q = 1) (hb : d92314 q = 1) : d94117 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82838, d94117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82838, d94117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d82839 q = 1) (hb : d92314 q = 1) : d94118 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82839, d94118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82839, d94118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d82840 q = 1) (hb : d92314 q = 1) : d94119 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82840, d94119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82840, d94119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d82841 q = 1) (hb : d92314 q = 1) : d94120 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82841, d94120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82841, d94120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82848 q = 1) (hb : d92314 q = 1) : d94127 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82848, d94127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82848, d94127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11579 q ha hb
  have h11 (q : Pattern) (ha : d82849 q = 1) (hb : d92314 q = 1) : d94128 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82849, d94128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82849, d94128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d82850 q = 1) (hb : d92314 q = 1) : d94129 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82850, d94129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82850, d94129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d82851 q = 1) (hb : d92314 q = 1) : d94130 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82851, d94130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82851, d94130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82852 q = 1) (hb : d92314 q = 1) : d94131 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82852, d94131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82852, d94131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d82853 q = 1) (hb : d92314 q = 1) : d94132 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82853, d94132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82853, d94132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11581 (p : Pattern) (ha : d82859 p = 1) (hb : d92314 p = 1) : d94138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82854 q = 1) (hb : d92314 q = 1) : d94133 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82854, d94133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82854, d94133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11580 q ha hb
  have h2 (q : Pattern) (ha : d82855 q = 1) (hb : d92314 q = 1) : d94134 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82855, d94134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82855, d94134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82856 q = 1) (hb : d92314 q = 1) : d94135 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82856, d94135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82856, d94135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82857 q = 1) (hb : d92314 q = 1) : d94136 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82857, d94136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82857, d94136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82858 q = 1) (hb : d92314 q = 1) : d94137 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82858, d94137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82858, d94137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82859 q = 1) (hb : d92314 q = 1) : d94138 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82859, d94138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82859, d94138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11582 (p : Pattern) (ha : d82865 p = 1) (hb : d92314 p = 1) : d94144 p = 1 := by
  have h0 (q : Pattern) (ha : d82746 q = 1) (hb : d92314 q = 1) : d94025 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82746, d94025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11561 q ha hb
    | true =>
      simp only [d82746, d94025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11565 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82773 q = 1) (hb : d92314 q = 1) : d94052 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82773, d94052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82773, d94052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11569 q ha hb
  have h3 (q : Pattern) (ha : d82774 q = 1) (hb : d92314 q = 1) : d94053 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82774, d94053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82774, d94053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82801 q = 1) (hb : d92314 q = 1) : d94080 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82801, d94080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82801, d94080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11573 q ha hb
  have h5 (q : Pattern) (ha : d82802 q = 1) (hb : d92314 q = 1) : d94081 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82802, d94081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82802, d94081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82803 q = 1) (hb : d92314 q = 1) : d94082 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82803, d94082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82803, d94082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82830 q = 1) (hb : d92314 q = 1) : d94109 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82830, d94109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82830, d94109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11577 q ha hb
  have h8 (q : Pattern) (ha : d82831 q = 1) (hb : d92314 q = 1) : d94110 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82831, d94110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82831, d94110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82832 q = 1) (hb : d92314 q = 1) : d94111 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82832, d94111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82832, d94111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82833 q = 1) (hb : d92314 q = 1) : d94112 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82833, d94112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82833, d94112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82860 q = 1) (hb : d92314 q = 1) : d94139 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82860, d94139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82860, d94139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11581 q ha hb
  have h12 (q : Pattern) (ha : d82861 q = 1) (hb : d92314 q = 1) : d94140 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82861, d94140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82861, d94140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82862 q = 1) (hb : d92314 q = 1) : d94141 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82862, d94141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82862, d94141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82863 q = 1) (hb : d92314 q = 1) : d94142 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82863, d94142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82863, d94142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82864 q = 1) (hb : d92314 q = 1) : d94143 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d82864, d94143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82864, d94143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82865 q = 1) (hb : d92314 q = 1) : d94144 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d82865, d94144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82865, d94144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro11583 (p : Pattern) (ha : d82871 p = 1) (hb : d92314 p = 1) : d94150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82866 q = 1) (hb : d92314 q = 1) : d94145 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d82866, d94145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11582 q ha hb
    | true =>
      simp only [d82866, d94145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82867 q = 1) (hb : d92314 q = 1) : d94146 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d82867, d94146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82867, d94146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82868 q = 1) (hb : d92314 q = 1) : d94147 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d82868, d94147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82868, d94147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82869 q = 1) (hb : d92314 q = 1) : d94148 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d82869, d94148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82869, d94148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82870 q = 1) (hb : d92314 q = 1) : d94149 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d82870, d94149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82870, d94149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82871 q = 1) (hb : d92314 q = 1) : d94150 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d82871, d94150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82871, d94150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11584 (p : Pattern) (ha : d82877 p = 1) (hb : d92314 p = 1) : d94156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82872 q = 1) (hb : d92314 q = 1) : d94151 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d82872, d94151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11583 q ha hb
    | true =>
      simp only [d82872, d94151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82873 q = 1) (hb : d92314 q = 1) : d94152 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d82873, d94152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82873, d94152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82874 q = 1) (hb : d92314 q = 1) : d94153 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d82874, d94153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82874, d94153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82875 q = 1) (hb : d92314 q = 1) : d94154 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d82875, d94154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82875, d94154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82876 q = 1) (hb : d92314 q = 1) : d94155 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d82876, d94155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82876, d94155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82877 q = 1) (hb : d92314 q = 1) : d94156 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d82877, d94156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82877, d94156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11585 (p : Pattern) (ha : d82883 p = 1) (hb : d92314 p = 1) : d94162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82878 q = 1) (hb : d92314 q = 1) : d94157 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82878, d94157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11584 q ha hb
    | true =>
      simp only [d82878, d94157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82879 q = 1) (hb : d92314 q = 1) : d94158 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82879, d94158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82879, d94158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82880 q = 1) (hb : d92314 q = 1) : d94159 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82880, d94159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82880, d94159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82881 q = 1) (hb : d92314 q = 1) : d94160 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82881, d94160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82881, d94160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82882 q = 1) (hb : d92314 q = 1) : d94161 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82882, d94161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82882, d94161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82883 q = 1) (hb : d92314 q = 1) : d94162 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82883, d94162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82883, d94162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11586 (p : Pattern) (ha : d82889 p = 1) (hb : d92314 p = 1) : d94168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82884 q = 1) (hb : d92314 q = 1) : d94163 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82884, d94163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11585 q ha hb
    | true =>
      simp only [d82884, d94163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82885 q = 1) (hb : d92314 q = 1) : d94164 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82885, d94164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82885, d94164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82886 q = 1) (hb : d92314 q = 1) : d94165 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82886, d94165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82886, d94165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82887 q = 1) (hb : d92314 q = 1) : d94166 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82887, d94166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82887, d94166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82888 q = 1) (hb : d92314 q = 1) : d94167 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82888, d94167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82888, d94167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82889 q = 1) (hb : d92314 q = 1) : d94168 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82889, d94168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82889, d94168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11587 (p : Pattern) (ha : d82895 p = 1) (hb : d92317 p = 1) : d94174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82890 q = 1) (hb : d92314 q = 1) : d94169 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82890, d94169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11586 q ha hb
    | true =>
      simp only [d82890, d94169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82891 q = 1) (hb : d92314 q = 1) : d94170 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82891, d94170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82891, d94170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92316 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d82892 q = 1) (hb : d92317 q = 1) : d94171 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82892, d92317, d94171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82892, d92317, d94171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d82893 q = 1) (hb : d92317 q = 1) : d94172 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82893, d94172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82893, d94172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82894 q = 1) (hb : d92317 q = 1) : d94173 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82894, d94173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82894, d94173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d82895 q = 1) (hb : d92317 q = 1) : d94174 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82895, d94174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82895, d94174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11588 (p : Pattern) (ha : d82901 p = 1) (hb : d92317 p = 1) : d94180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82896 q = 1) (hb : d92317 q = 1) : d94175 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82896, d94175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11587 q ha hb
    | true =>
      simp only [d82896, d94175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82897 q = 1) (hb : d92317 q = 1) : d94176 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82897, d94176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82897, d94176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82898 q = 1) (hb : d92317 q = 1) : d94177 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82898, d94177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82898, d94177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82899 q = 1) (hb : d92317 q = 1) : d94178 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82899, d94178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82899, d94178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82900 q = 1) (hb : d92317 q = 1) : d94179 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82900, d94179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82900, d94179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82901 q = 1) (hb : d92317 q = 1) : d94180 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82901, d94180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82901, d94180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11589 (p : Pattern) (ha : d82907 p = 1) (hb : d92317 p = 1) : d94186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82902 q = 1) (hb : d92317 q = 1) : d94181 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82902, d94181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11588 q ha hb
    | true =>
      simp only [d82902, d94181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82903 q = 1) (hb : d92317 q = 1) : d94182 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82903, d94182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82903, d94182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82904 q = 1) (hb : d92317 q = 1) : d94183 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82904, d94183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82904, d94183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82905 q = 1) (hb : d92317 q = 1) : d94184 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82905, d94184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82905, d94184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82906 q = 1) (hb : d92317 q = 1) : d94185 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82906, d94185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82906, d94185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82907 q = 1) (hb : d92317 q = 1) : d94186 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82907, d94186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82907, d94186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11590 (p : Pattern) (ha : d104 p = 1) (hb : d92327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d92323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d92323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d92323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d92324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d92324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d92324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d92325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d92325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d92325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d92326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d92326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d92326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d92327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d92327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d92327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11591 (p : Pattern) (ha : d111 p = 1) (hb : d92334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d92323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d92323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d92323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d92324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d92324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d92324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d92325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d92325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d92325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d92326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d92326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d92326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d107 q = 1) (hb : d92330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d92330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107, d92330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108 q = 1) (hb : d92331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d92331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108, d92331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109 q = 1) (hb : d92332 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d92332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109, d92332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d110 q = 1) (hb : d92333 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d92333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d110, d92333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d111 q = 1) (hb : d92334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d92334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d111, d92334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11592 (p : Pattern) (ha : d406 p = 1) (hb : d92341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d92330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d92330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d92330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d92331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d92331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d92331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d92339 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d92339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d92339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d92340 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d92340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d92340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d92341 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d92341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d92341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11593 (p : Pattern) (ha : d462 p = 1) (hb : d92356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d92352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d92352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d92352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d92353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d92353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d92353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d92354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d92354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d92354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d92355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d92355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d92355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d92356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d92356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d92356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11594 (p : Pattern) (ha : d53647 p = 1) (hb : d92362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d92335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d92335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11590 q ha hb
    | true =>
      simp only [d112, d92335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11591 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d92336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d92336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d92336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d92337 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d92337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d92337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d92338 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d92338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d92338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d92342 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d92342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d92342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11592 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d92343 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d92343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d92343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d92344 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d92344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d92344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d92345 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d92345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d92345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d92346 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d92346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d92346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d92357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d92357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d92357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11593 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d92358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d92358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d92358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d92359 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d92359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d92359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d92360 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d92360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d92360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d92361 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d92361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d92361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d92362 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d92362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d92362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11595 (p : Pattern) (ha : d92414 p = 1) (hb : d93315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92394 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92403 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92322 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11372 q hb ha
    | true =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d92404 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92404, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92410 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92411 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92411, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92412 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92412, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92413 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92413, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92414 q = 1) (hb : d93315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92414, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92414, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11596 (p : Pattern) (ha : d92433 p = 1) (hb : d93322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92403 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92322 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11372 q hb ha
    | true =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d92404 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92404, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92410 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92411 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92411, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92412 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92412, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92413 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92413, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92419 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92423 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92425 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92329 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11374 q hb ha
    | true =>
      simp only [d92329, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d92426 q = 1) (hb : d93318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92426, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92429 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92430 q = 1) (hb : d93319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92430, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92431 q = 1) (hb : d93320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92431, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92431, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92432 q = 1) (hb : d93321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92432, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92432, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92433 q = 1) (hb : d93322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92433, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92433, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11597 (p : Pattern) (ha : d92442 p = 1) (hb : d93976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92425 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92329 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11374 q hb ha
    | true =>
      simp only [d92329, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d92426 q = 1) (hb : d93318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92426, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92429 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92430 q = 1) (hb : d93319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92430, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92440 q = 1) (hb : d93320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92440, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92440, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92441 q = 1) (hb : d93321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92441, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92441, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92442 q = 1) (hb : d93976 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92442, d93976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92442, d93976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11598 (p : Pattern) (ha : d92467 p = 1) (hb : d93986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92351 q = 1) (hb : d93294 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92351, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11378 q hb ha
    | true =>
      simp only [d92351, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d92457 q = 1) (hb : d93982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92457, d93982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92457, d93982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92463 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92464 q = 1) (hb : d93983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92464, d93983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92464, d93983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92465 q = 1) (hb : d93984 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92465, d93984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92465, d93984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92466 q = 1) (hb : d93985 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92466, d93985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92466, d93985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92467 q = 1) (hb : d93986 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92467, d93986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92467, d93986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11599 (p : Pattern) (ha : d92473 p = 1) (hb : d93992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92382 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92434 q = 1) (hb : d93323 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92434, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11595 q ha hb
    | true =>
      simp only [d92434, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11596 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92437 q = 1) (hb : d93324 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92437, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92437, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92438 q = 1) (hb : d93974 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92438, d93974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92438, d93974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92439 q = 1) (hb : d93975 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92439, d93975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92439, d93975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92443 q = 1) (hb : d93977 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92443, d93977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92443, d93977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11597 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92444 q = 1) (hb : d93978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92444, d93978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92444, d93978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92445 q = 1) (hb : d93979 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92445, d93979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92445, d93979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92446 q = 1) (hb : d93980 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92446, d93980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92446, d93980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92447 q = 1) (hb : d93981 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92447, d93981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92447, d93981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92468 q = 1) (hb : d93987 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92468, d93987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92468, d93987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11598 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92469 q = 1) (hb : d93988 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92469, d93988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92469, d93988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92470 q = 1) (hb : d93989 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92470, d93989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92470, d93989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92471 q = 1) (hb : d93990 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92471, d93990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92471, d93990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92472 q = 1) (hb : d93991 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92472, d93991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92472, d93991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92473 q = 1) (hb : d93992 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92473, d93992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92473, d93992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11600 (p : Pattern) (ha : d92479 p = 1) (hb : d93998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d92363 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d92363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d92363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11594 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d92364 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d92364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d92364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d92365 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d92365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d92365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d92366 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d92366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d92366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d92367 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d92367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d92367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92474 q = 1) (hb : d93993 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92474, d93993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92474, d93993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11599 q ha hb
  have h8 (q : Pattern) (ha : d92475 q = 1) (hb : d93994 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92475, d93994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92475, d93994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92476 q = 1) (hb : d93995 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92476, d93995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92476, d93995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92477 q = 1) (hb : d93996 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92477, d93996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92477, d93996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92478 q = 1) (hb : d93997 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92478, d93997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92478, d93997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92479 q = 1) (hb : d93998 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92479, d93998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d92479, d93998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11601 (p : Pattern) (ha : d92538 p = 1) (hb : d93396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92507 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92513 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92527 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92484 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11402 q hb ha
    | true =>
      simp only [d92484, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h5 (q : Pattern) (ha : d92528 q = 1) (hb : d93392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92528, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92534 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92535 q = 1) (hb : d93393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92535, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92536 q = 1) (hb : d93394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92536, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92537 q = 1) (hb : d93395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92537, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92538 q = 1) (hb : d93396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92538, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92538, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11602 (p : Pattern) (ha : d92558 p = 1) (hb : d93404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92507 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92513 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92484 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11402 q hb ha
    | true =>
      simp only [d92484, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h4 (q : Pattern) (ha : d92528 q = 1) (hb : d93392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92528, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92535 q = 1) (hb : d93393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92535, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92536 q = 1) (hb : d93394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92536, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92537 q = 1) (hb : d93395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92537, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92543 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92550 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92493 q = 1) (hb : d93399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92493, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11404 q hb ha
    | true =>
      simp only [d92493, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h13 (q : Pattern) (ha : d92551 q = 1) (hb : d93400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92551, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92554 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92555 q = 1) (hb : d93401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92555, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92556 q = 1) (hb : d93402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92556, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92556, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92557 q = 1) (hb : d93403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92557, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92557, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92558 q = 1) (hb : d93404 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92558, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92558, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11603 (p : Pattern) (ha : d92572 p = 1) (hb : d94001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92550 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92493 q = 1) (hb : d93399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92493, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11404 q hb ha
    | true =>
      simp only [d92493, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h3 (q : Pattern) (ha : d92551 q = 1) (hb : d93400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92551, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92554 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92555 q = 1) (hb : d93401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92555, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92570 q = 1) (hb : d93402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92570, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92570, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92571 q = 1) (hb : d93403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92571, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92571, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92572 q = 1) (hb : d94001 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92572, d94001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92572, d94001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11604 (p : Pattern) (ha : d8555 p = 1) (hb : d92595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d92450 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d92450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11397 q ha hb
    | true =>
      simp only [d8378, d92450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d92451 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d92451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d92451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8552 q = 1) (hb : d92592 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8552, d92592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8552, d92592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8553 q = 1) (hb : d92593 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8553, d92593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8553, d92593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8554 q = 1) (hb : d92594 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8554, d92594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8554, d92594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8555 q = 1) (hb : d92595 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8555, d92595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8555, d92595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11605 (p : Pattern) (ha : d92607 p = 1) (hb : d94012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92591 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92596 q = 1) (hb : d94007 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92596, d94007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11604 q hb ha
    | true =>
      simp only [d92596, d94007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72 q hb ha
  have h3 (q : Pattern) (ha : d92597 q = 1) (hb : d94008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92597, d94008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92597, d94008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92604 q = 1) (hb : d94009 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92604, d94009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92604, d94009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92605 q = 1) (hb : d94010 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92605, d94010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92605, d94010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92606 q = 1) (hb : d94011 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92606, d94011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92606, d94011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92607 q = 1) (hb : d94012 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92607, d94012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92607, d94012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11606 (p : Pattern) (ha : d92613 p = 1) (hb : d94018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92501 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92559 q = 1) (hb : d93405 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92559, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11601 q ha hb
    | true =>
      simp only [d92559, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11602 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92566 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92567 q = 1) (hb : d93406 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92567, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92567, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92568 q = 1) (hb : d93999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92568, d93999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92568, d93999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92569 q = 1) (hb : d94000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92569, d94000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92569, d94000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92573 q = 1) (hb : d94002 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92573, d94002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92573, d94002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11603 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92574 q = 1) (hb : d94003 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92574, d94003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92574, d94003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92575 q = 1) (hb : d94004 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92575, d94004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92575, d94004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92576 q = 1) (hb : d94005 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92576, d94005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92576, d94005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92577 q = 1) (hb : d94006 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92577, d94006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92577, d94006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92608 q = 1) (hb : d94013 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92608, d94013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92608, d94013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11605 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92609 q = 1) (hb : d94014 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92609, d94014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92609, d94014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92610 q = 1) (hb : d94015 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92610, d94015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92610, d94015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92611 q = 1) (hb : d94016 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92611, d94016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92611, d94016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92612 q = 1) (hb : d94017 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92612, d94017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92612, d94017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92613 q = 1) (hb : d94018 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92613, d94018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92613, d94018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11607 (p : Pattern) (ha : d92619 p = 1) (hb : d94024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92614 q = 1) (hb : d94019 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92614, d94019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92614, d94019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11606 q ha hb
  have h2 (q : Pattern) (ha : d92615 q = 1) (hb : d94020 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92615, d94020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92615, d94020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92616 q = 1) (hb : d94021 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92616, d94021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92616, d94021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92617 q = 1) (hb : d94022 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92617, d94022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92617, d94022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92618 q = 1) (hb : d94023 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92618, d94023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92618, d94023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92619 q = 1) (hb : d94024 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92619, d94024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92619, d94024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11608 (p : Pattern) (ha : d92683 p = 1) (hb : d93502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92672 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92629 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11431 q hb ha
    | true =>
      simp only [d92629, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h5 (q : Pattern) (ha : d92673 q = 1) (hb : d93498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92673, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92679 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92680 q = 1) (hb : d93499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92680, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92681 q = 1) (hb : d93500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92681, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92682 q = 1) (hb : d93501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92682, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92683 q = 1) (hb : d93502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92683, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92683, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11609 (p : Pattern) (ha : d92703 p = 1) (hb : d93510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92629 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11431 q hb ha
    | true =>
      simp only [d92629, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h4 (q : Pattern) (ha : d92673 q = 1) (hb : d93498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92673, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92679 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92680 q = 1) (hb : d93499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92680, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92681 q = 1) (hb : d93500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92681, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92682 q = 1) (hb : d93501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92682, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92692 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92695 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92638 q = 1) (hb : d93505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92638, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11433 q hb ha
    | true =>
      simp only [d92638, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h13 (q : Pattern) (ha : d92696 q = 1) (hb : d93506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92696, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92699 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92700 q = 1) (hb : d93507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92700, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92701 q = 1) (hb : d93508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92701, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92701, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92702 q = 1) (hb : d93509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92702, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92702, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92703 q = 1) (hb : d93510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92703, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92703, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11610 (p : Pattern) (ha : d92717 p = 1) (hb : d94028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92638 q = 1) (hb : d93505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92638, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11433 q hb ha
    | true =>
      simp only [d92638, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h3 (q : Pattern) (ha : d92696 q = 1) (hb : d93506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92696, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92699 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92700 q = 1) (hb : d93507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92700, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92715 q = 1) (hb : d93508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92715, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92715, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92716 q = 1) (hb : d93509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92716, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92716, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92717 q = 1) (hb : d94028 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92717, d94028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92717, d94028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11611 (p : Pattern) (ha : d8721 p = 1) (hb : d92744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d92739 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d92739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11451 q ha hb
    | true =>
      simp only [d8716, d92739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d92740 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d92740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d92740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8718 q = 1) (hb : d92741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8718, d92741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8718, d92741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8719 q = 1) (hb : d92742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8719, d92742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8719, d92742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8720 q = 1) (hb : d92743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8720, d92743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8720, d92743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8721 q = 1) (hb : d92744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8721, d92744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8721, d92744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11612 (p : Pattern) (ha : d92756 p = 1) (hb : d94039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92736 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92745 q = 1) (hb : d94034 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92745, d94034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11611 q hb ha
    | true =>
      simp only [d92745, d94034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro118 q hb ha
  have h3 (q : Pattern) (ha : d92746 q = 1) (hb : d94035 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92746, d94035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92746, d94035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92752 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92753 q = 1) (hb : d94036 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92753, d94036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92753, d94036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92754 q = 1) (hb : d94037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92754, d94037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92754, d94037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92755 q = 1) (hb : d94038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92755, d94038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92755, d94038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92756 q = 1) (hb : d94039 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92756, d94039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92756, d94039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11613 (p : Pattern) (ha : d92762 p = 1) (hb : d94045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92646 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92704 q = 1) (hb : d93511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92704, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11608 q ha hb
    | true =>
      simp only [d92704, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11609 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92711 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92712 q = 1) (hb : d93512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92712, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92712, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92713 q = 1) (hb : d94026 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92713, d94026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92713, d94026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92714 q = 1) (hb : d94027 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92714, d94027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92714, d94027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92718 q = 1) (hb : d94029 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92718, d94029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92718, d94029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11610 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92719 q = 1) (hb : d94030 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92719, d94030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92719, d94030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92720 q = 1) (hb : d94031 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92720, d94031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92720, d94031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92721 q = 1) (hb : d94032 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92721, d94032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92721, d94032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92722 q = 1) (hb : d94033 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92722, d94033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92722, d94033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92757 q = 1) (hb : d94040 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92757, d94040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92757, d94040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11612 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92758 q = 1) (hb : d94041 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92758, d94041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92758, d94041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92759 q = 1) (hb : d94042 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92759, d94042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92759, d94042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92760 q = 1) (hb : d94043 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92760, d94043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92760, d94043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92761 q = 1) (hb : d94044 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92761, d94044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92761, d94044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92762 q = 1) (hb : d94045 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92762, d94045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92762, d94045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11614 (p : Pattern) (ha : d92768 p = 1) (hb : d94051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92763 q = 1) (hb : d94046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92763, d94046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92763, d94046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11613 q ha hb
  have h2 (q : Pattern) (ha : d92764 q = 1) (hb : d94047 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92764, d94047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92764, d94047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92765 q = 1) (hb : d94048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92765, d94048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92765, d94048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92766 q = 1) (hb : d94049 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92766, d94049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92766, d94049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92767 q = 1) (hb : d94050 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92767, d94050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92767, d94050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92768 q = 1) (hb : d94051 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92768, d94051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92768, d94051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11615 (p : Pattern) (ha : d92833 p = 1) (hb : d93609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92802 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92822 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92779 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11461 q hb ha
    | true =>
      simp only [d92779, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h5 (q : Pattern) (ha : d92823 q = 1) (hb : d93605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92823, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92829 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92830 q = 1) (hb : d93606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92830, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92831 q = 1) (hb : d93607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92831, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92832 q = 1) (hb : d93608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92832, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92833 q = 1) (hb : d93609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92833, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92833, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11616 (p : Pattern) (ha : d92853 p = 1) (hb : d93617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92822 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92779 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11461 q hb ha
    | true =>
      simp only [d92779, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h4 (q : Pattern) (ha : d92823 q = 1) (hb : d93605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92823, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92829 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92830 q = 1) (hb : d93606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92830, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92831 q = 1) (hb : d93607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92831, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92832 q = 1) (hb : d93608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92832, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92838 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92842 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92845 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92788 q = 1) (hb : d93612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92788, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11463 q hb ha
    | true =>
      simp only [d92788, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h13 (q : Pattern) (ha : d92846 q = 1) (hb : d93613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92846, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92849 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92850 q = 1) (hb : d93614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92850, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92851 q = 1) (hb : d93615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92851, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92851, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92852 q = 1) (hb : d93616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92852, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92852, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92853 q = 1) (hb : d93617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92853, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92853, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11617 (p : Pattern) (ha : d92867 p = 1) (hb : d94056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92788 q = 1) (hb : d93612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92788, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11463 q hb ha
    | true =>
      simp only [d92788, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h3 (q : Pattern) (ha : d92846 q = 1) (hb : d93613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92846, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92849 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92850 q = 1) (hb : d93614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92850, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92865 q = 1) (hb : d93615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92865, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92865, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92866 q = 1) (hb : d93616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92866, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92866, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92867 q = 1) (hb : d94056 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92867, d94056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92867, d94056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11618 (p : Pattern) (ha : d8888 p = 1) (hb : d92894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d92889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d92889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11481 q ha hb
    | true =>
      simp only [d8883, d92889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d92890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d92890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d92890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8885 q = 1) (hb : d92891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8885, d92891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8885, d92891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8886 q = 1) (hb : d92892 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8886, d92892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8886, d92892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8887 q = 1) (hb : d92893 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8887, d92893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8887, d92893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8888 q = 1) (hb : d92894 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8888, d92894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8888, d92894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11619 (p : Pattern) (ha : d92906 p = 1) (hb : d94067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92886 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92895 q = 1) (hb : d94062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92895, d94062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11618 q hb ha
    | true =>
      simp only [d92895, d94062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q hb ha
  have h3 (q : Pattern) (ha : d92896 q = 1) (hb : d94063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92896, d94063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92896, d94063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92903 q = 1) (hb : d94064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92903, d94064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92903, d94064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92904 q = 1) (hb : d94065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92904, d94065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92904, d94065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92905 q = 1) (hb : d94066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92905, d94066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92905, d94066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92906 q = 1) (hb : d94067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92906, d94067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92906, d94067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11620 (p : Pattern) (ha : d92912 p = 1) (hb : d94073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92796 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92854 q = 1) (hb : d93618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92854, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11615 q ha hb
    | true =>
      simp only [d92854, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11616 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92861 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92862 q = 1) (hb : d93619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92862, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92862, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92863 q = 1) (hb : d94054 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92863, d94054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92863, d94054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92864 q = 1) (hb : d94055 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92864, d94055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92864, d94055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92868 q = 1) (hb : d94057 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92868, d94057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92868, d94057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11617 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92869 q = 1) (hb : d94058 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92869, d94058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92869, d94058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92870 q = 1) (hb : d94059 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92870, d94059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92870, d94059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92871 q = 1) (hb : d94060 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92871, d94060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92871, d94060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92872 q = 1) (hb : d94061 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92872, d94061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92872, d94061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92907 q = 1) (hb : d94068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92907, d94068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92907, d94068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11619 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92908 q = 1) (hb : d94069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92908, d94069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92908, d94069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92909 q = 1) (hb : d94070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92909, d94070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92909, d94070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92910 q = 1) (hb : d94071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92910, d94071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92910, d94071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92911 q = 1) (hb : d94072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92911, d94072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92911, d94072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92912 q = 1) (hb : d94073 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92912, d94073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92912, d94073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11621 (p : Pattern) (ha : d92918 p = 1) (hb : d94079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92913 q = 1) (hb : d94074 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92913, d94074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92913, d94074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11620 q ha hb
  have h2 (q : Pattern) (ha : d92914 q = 1) (hb : d94075 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92914, d94075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92914, d94075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92915 q = 1) (hb : d94076 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92915, d94076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92915, d94076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92916 q = 1) (hb : d94077 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92916, d94077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92916, d94077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92917 q = 1) (hb : d94078 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92917, d94078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92917, d94078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92918 q = 1) (hb : d94079 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92918, d94079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92918, d94079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11622 (p : Pattern) (ha : d92984 p = 1) (hb : d93717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92953 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92959 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92973 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92930 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11491 q hb ha
    | true =>
      simp only [d92930, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h5 (q : Pattern) (ha : d92974 q = 1) (hb : d93713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92974, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92980 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92981 q = 1) (hb : d93714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92981, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92982 q = 1) (hb : d93715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92982, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92983 q = 1) (hb : d93716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92983, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92984 q = 1) (hb : d93717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92984, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92984, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11623 (p : Pattern) (ha : d93004 p = 1) (hb : d93725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92953 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92973 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92930 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11491 q hb ha
    | true =>
      simp only [d92930, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h4 (q : Pattern) (ha : d92974 q = 1) (hb : d93713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92974, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92980 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92981 q = 1) (hb : d93714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92981, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92982 q = 1) (hb : d93715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92982, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92983 q = 1) (hb : d93716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92983, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92989 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92993 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92996 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92939 q = 1) (hb : d93720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92939, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11493 q hb ha
    | true =>
      simp only [d92939, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h13 (q : Pattern) (ha : d92997 q = 1) (hb : d93721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92997, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d93000 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93001 q = 1) (hb : d93722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93001, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93002 q = 1) (hb : d93723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93002, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d93002, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93003 q = 1) (hb : d93724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93003, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d93003, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93004 q = 1) (hb : d93725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93004, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93004, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11624 (p : Pattern) (ha : d93018 p = 1) (hb : d94085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92939 q = 1) (hb : d93720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92939, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11493 q hb ha
    | true =>
      simp only [d92939, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h3 (q : Pattern) (ha : d92997 q = 1) (hb : d93721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92997, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93001 q = 1) (hb : d93722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93001, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93016 q = 1) (hb : d93723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93016, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93016, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93017 q = 1) (hb : d93724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93017, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93017, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93018 q = 1) (hb : d94085 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93018, d94085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93018, d94085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11625 (p : Pattern) (ha : d9056 p = 1) (hb : d93045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d93040 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d93040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11511 q ha hb
    | true =>
      simp only [d9051, d93040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d93041 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d93041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d93041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9053 q = 1) (hb : d93042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9053, d93042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9053, d93042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9054 q = 1) (hb : d93043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9054, d93043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9054, d93043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9055 q = 1) (hb : d93044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9055, d93044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9055, d93044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9056 q = 1) (hb : d93045 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9056, d93045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9056, d93045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11626 (p : Pattern) (ha : d93057 p = 1) (hb : d94096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d93046 q = 1) (hb : d94091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93046, d94091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11625 q hb ha
    | true =>
      simp only [d93046, d94091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q hb ha
  have h3 (q : Pattern) (ha : d93047 q = 1) (hb : d94092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93047, d94092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93047, d94092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93053 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93054 q = 1) (hb : d94093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93054, d94093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93054, d94093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93055 q = 1) (hb : d94094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93055, d94094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93055, d94094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93056 q = 1) (hb : d94095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93056, d94095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93056, d94095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93057 q = 1) (hb : d94096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93057, d94096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93057, d94096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11627 (p : Pattern) (ha : d93063 p = 1) (hb : d94102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92947 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93005 q = 1) (hb : d93726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93005, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11622 q ha hb
    | true =>
      simp only [d93005, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11623 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93013 q = 1) (hb : d93727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93013, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93013, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93014 q = 1) (hb : d94083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93014, d94083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93014, d94083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93015 q = 1) (hb : d94084 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93015, d94084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93015, d94084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93019 q = 1) (hb : d94086 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93019, d94086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93019, d94086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11624 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d93020 q = 1) (hb : d94087 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93020, d94087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93020, d94087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d93021 q = 1) (hb : d94088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93021, d94088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93021, d94088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d93022 q = 1) (hb : d94089 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93022, d94089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93022, d94089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d93023 q = 1) (hb : d94090 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93023, d94090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93023, d94090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93058 q = 1) (hb : d94097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93058, d94097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93058, d94097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11626 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93059 q = 1) (hb : d94098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93059, d94098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93059, d94098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93060 q = 1) (hb : d94099 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93060, d94099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93060, d94099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d93061 q = 1) (hb : d94100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93061, d94100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93061, d94100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d93062 q = 1) (hb : d94101 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93062, d94101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93062, d94101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d93063 q = 1) (hb : d94102 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93063, d94102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93063, d94102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11628 (p : Pattern) (ha : d93069 p = 1) (hb : d94108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93064 q = 1) (hb : d94103 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93064, d94103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93064, d94103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11627 q ha hb
  have h2 (q : Pattern) (ha : d93065 q = 1) (hb : d94104 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93065, d94104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93065, d94104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93066 q = 1) (hb : d94105 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93066, d94105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93066, d94105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93067 q = 1) (hb : d94106 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93067, d94106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93067, d94106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93068 q = 1) (hb : d94107 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93068, d94107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93068, d94107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93069 q = 1) (hb : d94108 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93069, d94108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93069, d94108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11629 (p : Pattern) (ha : d93136 p = 1) (hb : d93826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93111 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93082 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11521 q hb ha
    | true =>
      simp only [d93082, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h5 (q : Pattern) (ha : d93126 q = 1) (hb : d93822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d93126, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d93132 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d93133 q = 1) (hb : d93823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93133, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d93134 q = 1) (hb : d93824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93134, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93135 q = 1) (hb : d93825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93135, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93136 q = 1) (hb : d93826 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93136, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93136, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11630 (p : Pattern) (ha : d93156 p = 1) (hb : d93834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d93105 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93111 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93082 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11521 q hb ha
    | true =>
      simp only [d93082, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h4 (q : Pattern) (ha : d93126 q = 1) (hb : d93822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93126, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d93132 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93133 q = 1) (hb : d93823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93133, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93134 q = 1) (hb : d93824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93134, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93135 q = 1) (hb : d93825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93135, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d93141 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d93145 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d93148 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d93091 q = 1) (hb : d93829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93091, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11523 q hb ha
    | true =>
      simp only [d93091, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h13 (q : Pattern) (ha : d93149 q = 1) (hb : d93830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d93149, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d93152 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93153 q = 1) (hb : d93831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93153, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93154 q = 1) (hb : d93832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93154, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d93154, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93155 q = 1) (hb : d93833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93155, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d93155, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93156 q = 1) (hb : d93834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93156, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93156, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11631 (p : Pattern) (ha : d93170 p = 1) (hb : d94115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93148 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d93091 q = 1) (hb : d93829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93091, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11523 q hb ha
    | true =>
      simp only [d93091, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h3 (q : Pattern) (ha : d93149 q = 1) (hb : d93830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93149, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93153 q = 1) (hb : d93831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93153, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93168 q = 1) (hb : d93832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93168, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93168, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93169 q = 1) (hb : d93833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93169, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93169, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93170 q = 1) (hb : d94115 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93170, d94115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93170, d94115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11632 (p : Pattern) (ha : d9225 p = 1) (hb : d93197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d93192 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d93192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11541 q ha hb
    | true =>
      simp only [d9220, d93192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d93193 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d93193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d93193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9222 q = 1) (hb : d93194 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9222, d93194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9222, d93194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9223 q = 1) (hb : d93195 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9223, d93195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9223, d93195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9224 q = 1) (hb : d93196 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9224, d93196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9224, d93196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9225 q = 1) (hb : d93197 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9225, d93197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9225, d93197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11633 (p : Pattern) (ha : d93209 p = 1) (hb : d94126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d93198 q = 1) (hb : d94121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93198, d94121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11632 q hb ha
    | true =>
      simp only [d93198, d94121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q hb ha
  have h3 (q : Pattern) (ha : d93199 q = 1) (hb : d94122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93199, d94122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93199, d94122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93206 q = 1) (hb : d94123 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93206, d94123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93206, d94123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93207 q = 1) (hb : d94124 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93207, d94124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93207, d94124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93208 q = 1) (hb : d94125 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93208, d94125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93208, d94125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93209 q = 1) (hb : d94126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93209, d94126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93209, d94126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11634 (p : Pattern) (ha : d93215 p = 1) (hb : d94132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d93099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93157 q = 1) (hb : d93835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93157, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11629 q ha hb
    | true =>
      simp only [d93157, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11630 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93165 q = 1) (hb : d93836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93165, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93165, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93166 q = 1) (hb : d94113 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93166, d94113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93166, d94113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93167 q = 1) (hb : d94114 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93167, d94114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93167, d94114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93171 q = 1) (hb : d94116 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93171, d94116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93171, d94116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11631 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d93172 q = 1) (hb : d94117 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93172, d94117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93172, d94117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d93173 q = 1) (hb : d94118 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93173, d94118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93173, d94118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d93174 q = 1) (hb : d94119 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93174, d94119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93174, d94119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d93175 q = 1) (hb : d94120 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93175, d94120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93175, d94120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93210 q = 1) (hb : d94127 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93210, d94127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93210, d94127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11633 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93211 q = 1) (hb : d94128 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93211, d94128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93211, d94128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93212 q = 1) (hb : d94129 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93212, d94129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93212, d94129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d93213 q = 1) (hb : d94130 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93213, d94130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93213, d94130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d93214 q = 1) (hb : d94131 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93214, d94131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93214, d94131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d93215 q = 1) (hb : d94132 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93215, d94132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93215, d94132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11635 (p : Pattern) (ha : d93221 p = 1) (hb : d94138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93216 q = 1) (hb : d94133 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93216, d94133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93216, d94133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11634 q ha hb
  have h2 (q : Pattern) (ha : d93217 q = 1) (hb : d94134 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93217, d94134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93217, d94134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93218 q = 1) (hb : d94135 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93218, d94135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93218, d94135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93219 q = 1) (hb : d94136 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93219, d94136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93219, d94136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93220 q = 1) (hb : d94137 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93220, d94137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93220, d94137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93221 q = 1) (hb : d94138 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93221, d94138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93221, d94138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11636 (p : Pattern) (ha : d93227 p = 1) (hb : d94144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d92620 q = 1) (hb : d94025 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92620, d94025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11600 q ha hb
    | true =>
      simp only [d92620, d94025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11607 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92769 q = 1) (hb : d94052 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92769, d94052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92769, d94052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11614 q ha hb
  have h3 (q : Pattern) (ha : d92770 q = 1) (hb : d94053 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92770, d94053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d92770, d94053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92919 q = 1) (hb : d94080 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92919, d94080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92919, d94080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11621 q ha hb
  have h5 (q : Pattern) (ha : d92920 q = 1) (hb : d94081 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92920, d94081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92920, d94081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92921 q = 1) (hb : d94082 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d92921, d94082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92921, d94082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93070 q = 1) (hb : d94109 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93070, d94109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93070, d94109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11628 q ha hb
  have h8 (q : Pattern) (ha : d93071 q = 1) (hb : d94110 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93071, d94110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93071, d94110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93072 q = 1) (hb : d94111 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93072, d94111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93072, d94111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93073 q = 1) (hb : d94112 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93073, d94112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93073, d94112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93222 q = 1) (hb : d94139 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93222, d94139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93222, d94139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11635 q ha hb
  have h12 (q : Pattern) (ha : d93223 q = 1) (hb : d94140 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93223, d94140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93223, d94140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93224 q = 1) (hb : d94141 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93224, d94141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93224, d94141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93225 q = 1) (hb : d94142 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93225, d94142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93225, d94142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93226 q = 1) (hb : d94143 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d93226, d94143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93226, d94143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93227 q = 1) (hb : d94144 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d93227, d94144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93227, d94144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro11637 (p : Pattern) (ha : d93233 p = 1) (hb : d94150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93228 q = 1) (hb : d94145 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d93228, d94145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11636 q ha hb
    | true =>
      simp only [d93228, d94145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93229 q = 1) (hb : d94146 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d93229, d94146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93229, d94146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93230 q = 1) (hb : d94147 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d93230, d94147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93230, d94147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93231 q = 1) (hb : d94148 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d93231, d94148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93231, d94148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93232 q = 1) (hb : d94149 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d93232, d94149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93232, d94149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93233 q = 1) (hb : d94150 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d93233, d94150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93233, d94150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11638 (p : Pattern) (ha : d93239 p = 1) (hb : d94156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93234 q = 1) (hb : d94151 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d93234, d94151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11637 q ha hb
    | true =>
      simp only [d93234, d94151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93235 q = 1) (hb : d94152 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d93235, d94152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93235, d94152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93236 q = 1) (hb : d94153 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d93236, d94153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93236, d94153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93237 q = 1) (hb : d94154 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d93237, d94154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93237, d94154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93238 q = 1) (hb : d94155 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d93238, d94155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93238, d94155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93239 q = 1) (hb : d94156 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d93239, d94156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93239, d94156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11639 (p : Pattern) (ha : d93245 p = 1) (hb : d94162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93240 q = 1) (hb : d94157 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d93240, d94157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11638 q ha hb
    | true =>
      simp only [d93240, d94157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93241 q = 1) (hb : d94158 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d93241, d94158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93241, d94158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93242 q = 1) (hb : d94159 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d93242, d94159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93242, d94159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93243 q = 1) (hb : d94160 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d93243, d94160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93243, d94160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93244 q = 1) (hb : d94161 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d93244, d94161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93244, d94161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93245 q = 1) (hb : d94162 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d93245, d94162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93245, d94162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11640 (p : Pattern) (ha : d93251 p = 1) (hb : d94168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93246 q = 1) (hb : d94163 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d93246, d94163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11639 q ha hb
    | true =>
      simp only [d93246, d94163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93247 q = 1) (hb : d94164 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d93247, d94164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93247, d94164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93248 q = 1) (hb : d94165 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d93248, d94165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93248, d94165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93249 q = 1) (hb : d94166 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d93249, d94166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93249, d94166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93250 q = 1) (hb : d94167 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d93250, d94167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93250, d94167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93251 q = 1) (hb : d94168 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d93251, d94168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93251, d94168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11641 (p : Pattern) (ha : d93257 p = 1) (hb : d94174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93252 q = 1) (hb : d94169 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d93252, d94169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11640 q ha hb
    | true =>
      simp only [d93252, d94169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93253 q = 1) (hb : d94170 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d93253, d94170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93253, d94170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93254 q = 1) (hb : d94171 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d93254, d94171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93254, d94171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93255 q = 1) (hb : d94172 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d93255, d94172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93255, d94172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93256 q = 1) (hb : d94173 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d93256, d94173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93256, d94173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93257 q = 1) (hb : d94174 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d93257, d94174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93257, d94174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11642 (p : Pattern) (ha : d93263 p = 1) (hb : d94180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93258 q = 1) (hb : d94175 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d93258, d94175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11641 q ha hb
    | true =>
      simp only [d93258, d94175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93259 q = 1) (hb : d94176 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d93259, d94176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93259, d94176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93260 q = 1) (hb : d94177 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d93260, d94177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93260, d94177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93261 q = 1) (hb : d94178 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d93261, d94178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93261, d94178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93262 q = 1) (hb : d94179 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d93262, d94179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93262, d94179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93263 q = 1) (hb : d94180 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d93263, d94180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93263, d94180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11643 (p : Pattern) (ha : d93269 p = 1) (hb : d94186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93264 q = 1) (hb : d94181 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d93264, d94181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11642 q ha hb
    | true =>
      simp only [d93264, d94181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93265 q = 1) (hb : d94182 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d93265, d94182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93265, d94182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93266 q = 1) (hb : d94183 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d93266, d94183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93266, d94183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93267 q = 1) (hb : d94184 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d93267, d94184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93267, d94184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93268 q = 1) (hb : d94185 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d93268, d94185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93268, d94185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93269 q = 1) (hb : d94186 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d93269, d94186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93269, d94186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11644 (p : Pattern) (ha : d104 p = 1) (hb : d94191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8239 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d94187 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d94187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d94187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d94188 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d94188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d94188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d94189 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d94189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d94189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d94190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d94190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d94190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d94191 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d94191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d94191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11645 (p : Pattern) (ha : d111 p = 1) (hb : d94196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8239 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d94187 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d94187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d94187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d94188 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d94188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d94188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d94189 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d94189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d94189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d94190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d94190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d94190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8246 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d94192 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d94192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d94192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d94193 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d94193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d94193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d94194 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d94194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d94194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d94195 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d94195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d94195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d94196 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d94196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d94196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11646 (p : Pattern) (ha : d406 p = 1) (hb : d94203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d94192 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d94192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d94192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d94193 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d94193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d94193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d94201 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d94201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d94201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d94202 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d94202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d94202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d94203 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d94203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d94203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11647 (p : Pattern) (ha : d462 p = 1) (hb : d94213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8268 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d94209 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d94209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d94209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d94210 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d94210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d94210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d94211 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d94211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d94211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d94212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d94212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d94212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d94213 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d94213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d94213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11648 (p : Pattern) (ha : d53647 p = 1) (hb : d94219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d94197 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d94197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11644 q ha hb
    | true =>
      simp only [d112, d94197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11645 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d94198 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d94198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d94198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d94199 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d94199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d94199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d94200 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d94200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d94200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d94204 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d94204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d94204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11646 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d94205 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d94205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d94205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d94206 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d94206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d94206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d94207 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d94207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d94207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d94208 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d94208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d94208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d94214 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d94214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d94214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11647 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d94215 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d94215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d94215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d94216 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d94216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d94216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d94217 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d94217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d94217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d94218 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d94218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d94218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d94219 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d94219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d94219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11649 (p : Pattern) (ha : d93315 p = 1) (hb : d94229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8320 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93311 q = 1) (hb : d94225 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93311, d94225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93311, d94225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8336 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d93312 q = 1) (hb : d94226 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93312, d94226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93312, d94226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93313 q = 1) (hb : d94227 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93313, d94227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93313, d94227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93314 q = 1) (hb : d94228 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93314, d94228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93314, d94228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93315 q = 1) (hb : d94229 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93315, d94229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93315, d94229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11650 (p : Pattern) (ha : d93322 p = 1) (hb : d94234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93311 q = 1) (hb : d94225 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93311, d94225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93311, d94225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8336 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93312 q = 1) (hb : d94226 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93312, d94226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93312, d94226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93313 q = 1) (hb : d94227 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93313, d94227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93313, d94227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93314 q = 1) (hb : d94228 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93314, d94228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93314, d94228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8345 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8349 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8351 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d93318 q = 1) (hb : d94230 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93318, d94230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93318, d94230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93319 q = 1) (hb : d94231 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93319, d94231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93319, d94231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93320 q = 1) (hb : d94232 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93320, d94232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93320, d94232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93321 q = 1) (hb : d94233 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93321, d94233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93321, d94233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93322 q = 1) (hb : d94234 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93322, d94234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93322, d94234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11651 (p : Pattern) (ha : d93976 p = 1) (hb : d94241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93318 q = 1) (hb : d94230 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93318, d94230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93318, d94230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93319 q = 1) (hb : d94231 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93319, d94231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93319, d94231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93320 q = 1) (hb : d94239 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93320, d94239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93320, d94239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93321 q = 1) (hb : d94240 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93321, d94240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93321, d94240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93976 q = 1) (hb : d94241 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93976, d94241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93976, d94241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11652 (p : Pattern) (ha : d93986 p = 1) (hb : d94251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93294 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93982 q = 1) (hb : d94247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93982, d94247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93982, d94247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8400 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93983 q = 1) (hb : d94248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93983, d94248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93983, d94248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93984 q = 1) (hb : d94249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93984, d94249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93984, d94249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93985 q = 1) (hb : d94250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93985, d94250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93985, d94250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93986 q = 1) (hb : d94251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93986, d94251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93986, d94251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11653 (p : Pattern) (ha : d93992 p = 1) (hb : d94257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93323 q = 1) (hb : d94235 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93323, d94235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11649 q ha hb
    | true =>
      simp only [d93323, d94235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11650 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8364 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93324 q = 1) (hb : d94236 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93324, d94236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93324, d94236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93974 q = 1) (hb : d94237 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93974, d94237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93974, d94237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93975 q = 1) (hb : d94238 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93975, d94238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93975, d94238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93977 q = 1) (hb : d94242 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93977, d94242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93977, d94242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11651 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d93978 q = 1) (hb : d94243 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93978, d94243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93978, d94243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93979 q = 1) (hb : d94244 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93979, d94244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93979, d94244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d93980 q = 1) (hb : d94245 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93980, d94245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93980, d94245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d93981 q = 1) (hb : d94246 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93981, d94246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93981, d94246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93987 q = 1) (hb : d94252 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93987, d94252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93987, d94252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11652 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93988 q = 1) (hb : d94253 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93988, d94253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93988, d94253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93989 q = 1) (hb : d94254 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93989, d94254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93989, d94254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d93990 q = 1) (hb : d94255 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93990, d94255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93990, d94255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d93991 q = 1) (hb : d94256 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93991, d94256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93991, d94256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d93992 q = 1) (hb : d94257 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93992, d94257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93992, d94257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11654 (p : Pattern) (ha : d93998 p = 1) (hb : d94263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d94220 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d94220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d94220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11648 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d94221 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d94221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d94221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d94222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d94222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d94222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d94223 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d94223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d94223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d94224 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d94224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d94224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93993 q = 1) (hb : d94258 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93993, d94258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93993, d94258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11653 q ha hb
  have h8 (q : Pattern) (ha : d93994 q = 1) (hb : d94259 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93994, d94259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93994, d94259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93995 q = 1) (hb : d94260 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93995, d94260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93995, d94260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93996 q = 1) (hb : d94261 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93996, d94261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93996, d94261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93997 q = 1) (hb : d94262 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93997, d94262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93997, d94262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d93998 q = 1) (hb : d94263 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93998, d94263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93998, d94263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11655 (p : Pattern) (ha : d93396 p = 1) (hb : d94268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8444 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8450 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8464 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93392 q = 1) (hb : d94264 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93392, d94264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93392, d94264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8481 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d93393 q = 1) (hb : d94265 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93393, d94265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93393, d94265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93394 q = 1) (hb : d94266 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93394, d94266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93394, d94266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93395 q = 1) (hb : d94267 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93395, d94267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93395, d94267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93396 q = 1) (hb : d94268 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93396, d94268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93396, d94268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11656 (p : Pattern) (ha : d93404 p = 1) (hb : d94273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8450 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8464 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93392 q = 1) (hb : d94264 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93392, d94264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93392, d94264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8481 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93393 q = 1) (hb : d94265 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93393, d94265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93393, d94265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93394 q = 1) (hb : d94266 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93394, d94266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93394, d94266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93395 q = 1) (hb : d94267 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93395, d94267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93395, d94267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8490 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8494 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8497 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93399 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d93400 q = 1) (hb : d94269 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93400, d94269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93400, d94269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8503 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93401 q = 1) (hb : d94270 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93401, d94270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93401, d94270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93402 q = 1) (hb : d94271 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93402, d94271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93402, d94271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93403 q = 1) (hb : d94272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93403, d94272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93403, d94272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93404 q = 1) (hb : d94273 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93404, d94273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93404, d94273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11657 (p : Pattern) (ha : d94001 p = 1) (hb : d94280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93399 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93400 q = 1) (hb : d94269 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93400, d94269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93400, d94269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8503 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93401 q = 1) (hb : d94270 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93401, d94270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93401, d94270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93402 q = 1) (hb : d94278 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93402, d94278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93402, d94278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93403 q = 1) (hb : d94279 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93403, d94279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93403, d94279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94001 q = 1) (hb : d94280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94001, d94280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94001, d94280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11658 (p : Pattern) (ha : d94012 p = 1) (hb : d94290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94007 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94008 q = 1) (hb : d94286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94008, d94286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94008, d94286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8557 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94009 q = 1) (hb : d94287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94009, d94287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94009, d94287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94010 q = 1) (hb : d94288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94010, d94288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94010, d94288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94011 q = 1) (hb : d94289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94011, d94289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94011, d94289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94012 q = 1) (hb : d94290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94012, d94290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94012, d94290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11659 (p : Pattern) (ha : d94018 p = 1) (hb : d94296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8438 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93405 q = 1) (hb : d94274 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93405, d94274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11655 q ha hb
    | true =>
      simp only [d93405, d94274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11656 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93406 q = 1) (hb : d94275 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93406, d94275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93406, d94275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93999 q = 1) (hb : d94276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93999, d94276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93999, d94276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94000 q = 1) (hb : d94277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94000, d94277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94000, d94277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94002 q = 1) (hb : d94281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94002, d94281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94002, d94281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11657 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94003 q = 1) (hb : d94282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94003, d94282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94003, d94282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94004 q = 1) (hb : d94283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94004, d94283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94004, d94283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94005 q = 1) (hb : d94284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94005, d94284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94005, d94284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94006 q = 1) (hb : d94285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94006, d94285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94006, d94285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94013 q = 1) (hb : d94291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94013, d94291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94013, d94291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11658 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94014 q = 1) (hb : d94292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94014, d94292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94014, d94292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94015 q = 1) (hb : d94293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94015, d94293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94015, d94293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94016 q = 1) (hb : d94294 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94016, d94294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94016, d94294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94017 q = 1) (hb : d94295 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94017, d94295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94017, d94295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94018 q = 1) (hb : d94296 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94018, d94296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94018, d94296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11660 (p : Pattern) (ha : d94024 p = 1) (hb : d94302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94019 q = 1) (hb : d94297 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94019, d94297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94019, d94297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11659 q ha hb
  have h2 (q : Pattern) (ha : d94020 q = 1) (hb : d94298 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94020, d94298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94020, d94298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94021 q = 1) (hb : d94299 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94021, d94299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94021, d94299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94022 q = 1) (hb : d94300 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94022, d94300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94022, d94300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94023 q = 1) (hb : d94301 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94023, d94301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94023, d94301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94024 q = 1) (hb : d94302 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94024, d94302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94024, d94302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11661 (p : Pattern) (ha : d93502 p = 1) (hb : d94308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8606 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8612 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93498 q = 1) (hb : d94304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93498, d94304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93498, d94304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8643 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d93499 q = 1) (hb : d94305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93499, d94305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93499, d94305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93500 q = 1) (hb : d94306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93500, d94306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93500, d94306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93501 q = 1) (hb : d94307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93501, d94307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93501, d94307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93502 q = 1) (hb : d94308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93502, d94308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93502, d94308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11662 (p : Pattern) (ha : d93510 p = 1) (hb : d94313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8606 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93498 q = 1) (hb : d94304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93498, d94304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93498, d94304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8643 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93499 q = 1) (hb : d94305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93499, d94305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93499, d94305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93500 q = 1) (hb : d94306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93500, d94306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93500, d94306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93501 q = 1) (hb : d94307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93501, d94307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93501, d94307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8652 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8656 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8659 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93505 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d93506 q = 1) (hb : d94309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93506, d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93506, d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8665 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93507 q = 1) (hb : d94310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93507, d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93507, d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93508 q = 1) (hb : d94311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93508, d94311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93508, d94311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93509 q = 1) (hb : d94312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93509, d94312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93509, d94312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93510 q = 1) (hb : d94313 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93510, d94313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93510, d94313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11663 (p : Pattern) (ha : d94028 p = 1) (hb : d94320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93506 q = 1) (hb : d94309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93506, d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93506, d94309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8665 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93507 q = 1) (hb : d94310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93507, d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93507, d94310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93508 q = 1) (hb : d94318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93508, d94318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93508, d94318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93509 q = 1) (hb : d94319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93509, d94319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93509, d94319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94028 q = 1) (hb : d94320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94028, d94320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94028, d94320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11664 (p : Pattern) (ha : d94039 p = 1) (hb : d94330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8702 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94034 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94035 q = 1) (hb : d94326 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94035, d94326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94035, d94326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8723 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94036 q = 1) (hb : d94327 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94036, d94327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94036, d94327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94037 q = 1) (hb : d94328 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94037, d94328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94037, d94328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94038 q = 1) (hb : d94329 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94038, d94329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94038, d94329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94039 q = 1) (hb : d94330 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94039, d94330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94039, d94330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11665 (p : Pattern) (ha : d94045 p = 1) (hb : d94336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8600 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93511 q = 1) (hb : d94314 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93511, d94314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11661 q ha hb
    | true =>
      simp only [d93511, d94314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11662 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8677 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93512 q = 1) (hb : d94315 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93512, d94315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93512, d94315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94026 q = 1) (hb : d94316 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94026, d94316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94026, d94316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94027 q = 1) (hb : d94317 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94027, d94317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94027, d94317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94029 q = 1) (hb : d94321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94029, d94321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94029, d94321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11663 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94030 q = 1) (hb : d94322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94030, d94322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94030, d94322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94031 q = 1) (hb : d94323 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94031, d94323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94031, d94323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94032 q = 1) (hb : d94324 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94032, d94324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94032, d94324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94033 q = 1) (hb : d94325 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94033, d94325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94033, d94325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94040 q = 1) (hb : d94331 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94040, d94331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94040, d94331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11664 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94041 q = 1) (hb : d94332 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94041, d94332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94041, d94332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94042 q = 1) (hb : d94333 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94042, d94333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94042, d94333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94043 q = 1) (hb : d94334 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94043, d94334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94043, d94334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94044 q = 1) (hb : d94335 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94044, d94335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94044, d94335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94045 q = 1) (hb : d94336 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94045, d94336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94045, d94336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11666 (p : Pattern) (ha : d94051 p = 1) (hb : d94342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94046 q = 1) (hb : d94337 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94046, d94337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94046, d94337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11665 q ha hb
  have h2 (q : Pattern) (ha : d94047 q = 1) (hb : d94338 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94047, d94338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94047, d94338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94048 q = 1) (hb : d94339 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94048, d94339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94048, d94339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94049 q = 1) (hb : d94340 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94049, d94340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94049, d94340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94050 q = 1) (hb : d94341 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94050, d94341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94050, d94341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94051 q = 1) (hb : d94342 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94051, d94342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94051, d94342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11667 (p : Pattern) (ha : d93609 p = 1) (hb : d94349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8793 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93605 q = 1) (hb : d94345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93605, d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93605, d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8810 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d93606 q = 1) (hb : d94346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93606, d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93606, d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93607 q = 1) (hb : d94347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93607, d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93607, d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93608 q = 1) (hb : d94348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93608, d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93608, d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93609 q = 1) (hb : d94349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93609, d94349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93609, d94349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11668 (p : Pattern) (ha : d93617 p = 1) (hb : d94354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93605 q = 1) (hb : d94345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93605, d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93605, d94345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8810 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93606 q = 1) (hb : d94346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93606, d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93606, d94346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93607 q = 1) (hb : d94347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93607, d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93607, d94347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93608 q = 1) (hb : d94348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93608, d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93608, d94348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8819 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8823 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8826 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93612 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d93613 q = 1) (hb : d94350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93613, d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93613, d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8832 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93614 q = 1) (hb : d94351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93614, d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93614, d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93615 q = 1) (hb : d94352 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93615, d94352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93615, d94352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93616 q = 1) (hb : d94353 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93616, d94353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93616, d94353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93617 q = 1) (hb : d94354 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93617, d94354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93617, d94354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11669 (p : Pattern) (ha : d94056 p = 1) (hb : d94361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93612 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93613 q = 1) (hb : d94350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93613, d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93613, d94350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93614 q = 1) (hb : d94351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93614, d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93614, d94351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93615 q = 1) (hb : d94359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93615, d94359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93615, d94359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93616 q = 1) (hb : d94360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93616, d94360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93616, d94360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94056 q = 1) (hb : d94361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94056, d94361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94056, d94361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11670 (p : Pattern) (ha : d94067 p = 1) (hb : d94371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8869 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94062 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94063 q = 1) (hb : d94367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94063, d94367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94063, d94367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94064 q = 1) (hb : d94368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94064, d94368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94064, d94368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94065 q = 1) (hb : d94369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94065, d94369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94065, d94369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94066 q = 1) (hb : d94370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94066, d94370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94066, d94370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94067 q = 1) (hb : d94371 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94067, d94371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94067, d94371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11671 (p : Pattern) (ha : d94073 p = 1) (hb : d94377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93618 q = 1) (hb : d94355 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93618, d94355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11667 q ha hb
    | true =>
      simp only [d93618, d94355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11668 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8844 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93619 q = 1) (hb : d94356 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93619, d94356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93619, d94356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94054 q = 1) (hb : d94357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94054, d94357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94054, d94357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94055 q = 1) (hb : d94358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94055, d94358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94055, d94358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94057 q = 1) (hb : d94362 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94057, d94362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94057, d94362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11669 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94058 q = 1) (hb : d94363 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94058, d94363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94058, d94363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94059 q = 1) (hb : d94364 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94059, d94364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94059, d94364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94060 q = 1) (hb : d94365 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94060, d94365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94060, d94365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94061 q = 1) (hb : d94366 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94061, d94366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94061, d94366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94068 q = 1) (hb : d94372 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94068, d94372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94068, d94372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11670 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94069 q = 1) (hb : d94373 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94069, d94373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94069, d94373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94070 q = 1) (hb : d94374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94070, d94374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94070, d94374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94071 q = 1) (hb : d94375 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94071, d94375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94071, d94375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94072 q = 1) (hb : d94376 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94072, d94376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94072, d94376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94073 q = 1) (hb : d94377 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94073, d94377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94073, d94377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11672 (p : Pattern) (ha : d94079 p = 1) (hb : d94383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94074 q = 1) (hb : d94378 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94074, d94378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94074, d94378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11671 q ha hb
  have h2 (q : Pattern) (ha : d94075 q = 1) (hb : d94379 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94075, d94379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94075, d94379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94076 q = 1) (hb : d94380 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94076, d94380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94076, d94380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94077 q = 1) (hb : d94381 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94077, d94381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94077, d94381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94078 q = 1) (hb : d94382 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94078, d94382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94078, d94382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94079 q = 1) (hb : d94383 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94079, d94383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94079, d94383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11673 (p : Pattern) (ha : d93717 p = 1) (hb : d94391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8947 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8961 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93713 q = 1) (hb : d94387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93713, d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93713, d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8978 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d93714 q = 1) (hb : d94388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93714, d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93714, d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93715 q = 1) (hb : d94389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93715, d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93715, d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93716 q = 1) (hb : d94390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93716, d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93716, d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93717 q = 1) (hb : d94391 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93717, d94391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93717, d94391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11674 (p : Pattern) (ha : d93725 p = 1) (hb : d94396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8947 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8961 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93713 q = 1) (hb : d94387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93713, d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93713, d94387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8978 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93714 q = 1) (hb : d94388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93714, d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93714, d94388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93715 q = 1) (hb : d94389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93715, d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93715, d94389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93716 q = 1) (hb : d94390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93716, d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93716, d94390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8987 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8991 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8994 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93720 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d93721 q = 1) (hb : d94392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93721, d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93721, d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9000 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93722 q = 1) (hb : d94393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93722, d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93722, d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93723 q = 1) (hb : d94394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93723, d94394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93723, d94394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93724 q = 1) (hb : d94395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93724, d94395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93724, d94395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93725 q = 1) (hb : d94396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93725, d94396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93725, d94396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11675 (p : Pattern) (ha : d94085 p = 1) (hb : d94403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93720 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93721 q = 1) (hb : d94392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93721, d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93721, d94392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93722 q = 1) (hb : d94393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93722, d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93722, d94393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93723 q = 1) (hb : d94401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93723, d94401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93723, d94401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93724 q = 1) (hb : d94402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93724, d94402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93724, d94402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94085 q = 1) (hb : d94403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94085, d94403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94085, d94403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11676 (p : Pattern) (ha : d94096 p = 1) (hb : d94413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94092 q = 1) (hb : d94409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94092, d94409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94092, d94409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9058 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94093 q = 1) (hb : d94410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94093, d94410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94093, d94410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94094 q = 1) (hb : d94411 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94094, d94411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94094, d94411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94095 q = 1) (hb : d94412 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94095, d94412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94095, d94412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94096 q = 1) (hb : d94413 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94096, d94413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94096, d94413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11677 (p : Pattern) (ha : d94102 p = 1) (hb : d94419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93726 q = 1) (hb : d94397 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93726, d94397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11673 q ha hb
    | true =>
      simp only [d93726, d94397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11674 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93727 q = 1) (hb : d94398 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93727, d94398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93727, d94398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94083 q = 1) (hb : d94399 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94083, d94399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94083, d94399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94084 q = 1) (hb : d94400 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94084, d94400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94084, d94400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94086 q = 1) (hb : d94404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94086, d94404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94086, d94404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11675 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94087 q = 1) (hb : d94405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94087, d94405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94087, d94405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94088 q = 1) (hb : d94406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94088, d94406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94088, d94406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94089 q = 1) (hb : d94407 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94089, d94407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94089, d94407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94090 q = 1) (hb : d94408 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94090, d94408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94090, d94408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94097 q = 1) (hb : d94414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94097, d94414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94097, d94414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11676 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94098 q = 1) (hb : d94415 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94098, d94415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94098, d94415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94099 q = 1) (hb : d94416 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94099, d94416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94099, d94416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94100 q = 1) (hb : d94417 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94100, d94417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94100, d94417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94101 q = 1) (hb : d94418 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94101, d94418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94101, d94418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94102 q = 1) (hb : d94419 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94102, d94419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94102, d94419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11678 (p : Pattern) (ha : d94108 p = 1) (hb : d94425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94103 q = 1) (hb : d94420 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94103, d94420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94103, d94420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11677 q ha hb
  have h2 (q : Pattern) (ha : d94104 q = 1) (hb : d94421 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94104, d94421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94104, d94421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94105 q = 1) (hb : d94422 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94105, d94422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94105, d94422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94106 q = 1) (hb : d94423 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94106, d94423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94106, d94423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94107 q = 1) (hb : d94424 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94107, d94424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94107, d94424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94108 q = 1) (hb : d94425 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94108, d94425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94108, d94425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11679 (p : Pattern) (ha : d93826 p = 1) (hb : d94434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9116 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d9130 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93822 q = 1) (hb : d94430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93822, d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93822, d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d93823 q = 1) (hb : d94431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93823, d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93823, d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93824 q = 1) (hb : d94432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93824, d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93824, d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93825 q = 1) (hb : d94433 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93825, d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93825, d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93826 q = 1) (hb : d94434 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93826, d94434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93826, d94434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11680 (p : Pattern) (ha : d93834 p = 1) (hb : d94439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9110 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9116 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93822 q = 1) (hb : d94430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93822, d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93822, d94430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9147 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93823 q = 1) (hb : d94431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93823, d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93823, d94431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93824 q = 1) (hb : d94432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93824, d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93824, d94432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93825 q = 1) (hb : d94433 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93825, d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93825, d94433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9156 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d9160 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9163 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93829 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d93830 q = 1) (hb : d94435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93830, d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93830, d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9169 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93831 q = 1) (hb : d94436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93831, d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93831, d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93832 q = 1) (hb : d94437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93832, d94437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93832, d94437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93833 q = 1) (hb : d94438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93833, d94438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93833, d94438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93834 q = 1) (hb : d94439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93834, d94439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93834, d94439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11681 (p : Pattern) (ha : d94115 p = 1) (hb : d94446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9163 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93829 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93830 q = 1) (hb : d94435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93830, d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93830, d94435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9169 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93831 q = 1) (hb : d94436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93831, d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93831, d94436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93832 q = 1) (hb : d94444 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93832, d94444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93832, d94444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93833 q = 1) (hb : d94445 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93833, d94445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d93833, d94445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94115 q = 1) (hb : d94446 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94115, d94446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94115, d94446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11682 (p : Pattern) (ha : d94126 p = 1) (hb : d94456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9206 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94122 q = 1) (hb : d94452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94122, d94452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94122, d94452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9227 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94123 q = 1) (hb : d94453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94123, d94453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94123, d94453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94124 q = 1) (hb : d94454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94124, d94454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94124, d94454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94125 q = 1) (hb : d94455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94125, d94455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94125, d94455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94126 q = 1) (hb : d94456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94126, d94456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94126, d94456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11683 (p : Pattern) (ha : d94132 p = 1) (hb : d94462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9104 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93835 q = 1) (hb : d94440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93835, d94440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11679 q ha hb
    | true =>
      simp only [d93835, d94440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11680 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93836 q = 1) (hb : d94441 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93836, d94441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93836, d94441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94113 q = 1) (hb : d94442 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94113, d94442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94113, d94442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94114 q = 1) (hb : d94443 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94114, d94443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94114, d94443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94116 q = 1) (hb : d94447 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94116, d94447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94116, d94447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11681 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94117 q = 1) (hb : d94448 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94117, d94448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94117, d94448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94118 q = 1) (hb : d94449 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94118, d94449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94118, d94449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94119 q = 1) (hb : d94450 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94119, d94450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94119, d94450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94120 q = 1) (hb : d94451 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94120, d94451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94120, d94451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94127 q = 1) (hb : d94457 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94127, d94457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94127, d94457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11682 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94128 q = 1) (hb : d94458 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94128, d94458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94128, d94458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94129 q = 1) (hb : d94459 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94129, d94459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94129, d94459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94130 q = 1) (hb : d94460 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94130, d94460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94130, d94460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94131 q = 1) (hb : d94461 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94131, d94461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94131, d94461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94132 q = 1) (hb : d94462 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94132, d94462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94132, d94462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11684 (p : Pattern) (ha : d94138 p = 1) (hb : d94468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94133 q = 1) (hb : d94463 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94133, d94463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94133, d94463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11683 q ha hb
  have h2 (q : Pattern) (ha : d94134 q = 1) (hb : d94464 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94134, d94464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94134, d94464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94135 q = 1) (hb : d94465 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94135, d94465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94135, d94465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94136 q = 1) (hb : d94466 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94136, d94466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94136, d94466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94137 q = 1) (hb : d94467 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94137, d94467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94137, d94467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94138 q = 1) (hb : d94468 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94138, d94468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94138, d94468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11685 (p : Pattern) (ha : d94144 p = 1) (hb : d94474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d94025 q = 1) (hb : d94303 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94025, d94303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11654 q ha hb
    | true =>
      simp only [d94025, d94303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11660 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94052 q = 1) (hb : d94343 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94052, d94343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94052, d94343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11666 q ha hb
  have h3 (q : Pattern) (ha : d94053 q = 1) (hb : d94344 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94053, d94344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94053, d94344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94080 q = 1) (hb : d94384 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94080, d94384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94080, d94384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11672 q ha hb
  have h5 (q : Pattern) (ha : d94081 q = 1) (hb : d94385 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94081, d94385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94081, d94385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94082 q = 1) (hb : d94386 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94082, d94386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94082, d94386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94109 q = 1) (hb : d94426 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94109, d94426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94109, d94426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11678 q ha hb
  have h8 (q : Pattern) (ha : d94110 q = 1) (hb : d94427 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94110, d94427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94110, d94427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94111 q = 1) (hb : d94428 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94111, d94428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94111, d94428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94112 q = 1) (hb : d94429 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94112, d94429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94112, d94429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94139 q = 1) (hb : d94469 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94139, d94469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94139, d94469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11684 q ha hb
  have h12 (q : Pattern) (ha : d94140 q = 1) (hb : d94470 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94140, d94470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94140, d94470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94141 q = 1) (hb : d94471 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94141, d94471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94141, d94471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94142 q = 1) (hb : d94472 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94142, d94472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94142, d94472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94143 q = 1) (hb : d94473 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94143, d94473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94143, d94473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94144 q = 1) (hb : d94474 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94144, d94474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94144, d94474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro11686 (p : Pattern) (ha : d94150 p = 1) (hb : d94480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94145 q = 1) (hb : d94475 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94145, d94475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11685 q ha hb
    | true =>
      simp only [d94145, d94475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94146 q = 1) (hb : d94476 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94146, d94476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94146, d94476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94147 q = 1) (hb : d94477 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94147, d94477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94147, d94477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94148 q = 1) (hb : d94478 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94148, d94478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94148, d94478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94149 q = 1) (hb : d94479 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94149, d94479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94149, d94479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94150 q = 1) (hb : d94480 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94150, d94480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94150, d94480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11687 (p : Pattern) (ha : d94156 p = 1) (hb : d94486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94151 q = 1) (hb : d94481 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94151, d94481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11686 q ha hb
    | true =>
      simp only [d94151, d94481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94152 q = 1) (hb : d94482 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94152, d94482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94152, d94482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94153 q = 1) (hb : d94483 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94153, d94483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94153, d94483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94154 q = 1) (hb : d94484 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94154, d94484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94154, d94484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94155 q = 1) (hb : d94485 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94155, d94485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94155, d94485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94156 q = 1) (hb : d94486 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94156, d94486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94156, d94486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11688 (p : Pattern) (ha : d94162 p = 1) (hb : d94492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94157 q = 1) (hb : d94487 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94157, d94487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11687 q ha hb
    | true =>
      simp only [d94157, d94487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94158 q = 1) (hb : d94488 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94158, d94488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94158, d94488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94159 q = 1) (hb : d94489 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94159, d94489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94159, d94489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94160 q = 1) (hb : d94490 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94160, d94490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94160, d94490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94161 q = 1) (hb : d94491 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94161, d94491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94161, d94491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94162 q = 1) (hb : d94492 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94162, d94492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94162, d94492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11689 (p : Pattern) (ha : d94168 p = 1) (hb : d94498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94163 q = 1) (hb : d94493 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94163, d94493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11688 q ha hb
    | true =>
      simp only [d94163, d94493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94164 q = 1) (hb : d94494 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94164, d94494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94164, d94494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94165 q = 1) (hb : d94495 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94165, d94495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94165, d94495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94166 q = 1) (hb : d94496 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94166, d94496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94166, d94496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94167 q = 1) (hb : d94497 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94167, d94497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94167, d94497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94168 q = 1) (hb : d94498 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94168, d94498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94168, d94498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11690 (p : Pattern) (ha : d94174 p = 1) (hb : d94504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94169 q = 1) (hb : d94499 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94169, d94499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11689 q ha hb
    | true =>
      simp only [d94169, d94499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94170 q = 1) (hb : d94500 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94170, d94500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94170, d94500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94171 q = 1) (hb : d94501 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94171, d94501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94171, d94501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94172 q = 1) (hb : d94502 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94172, d94502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94172, d94502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94173 q = 1) (hb : d94503 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94173, d94503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94173, d94503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94174 q = 1) (hb : d94504 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94174, d94504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94174, d94504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11691 (p : Pattern) (ha : d94180 p = 1) (hb : d94510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94175 q = 1) (hb : d94505 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94175, d94505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11690 q ha hb
    | true =>
      simp only [d94175, d94505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94176 q = 1) (hb : d94506 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94176, d94506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94176, d94506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94177 q = 1) (hb : d94507 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94177, d94507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94177, d94507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94178 q = 1) (hb : d94508 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94178, d94508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94178, d94508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94179 q = 1) (hb : d94509 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94179, d94509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94179, d94509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94180 q = 1) (hb : d94510 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94180, d94510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94180, d94510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11692 (p : Pattern) (ha : d94186 p = 1) (hb : d94516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94181 q = 1) (hb : d94511 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94181, d94511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11691 q ha hb
    | true =>
      simp only [d94181, d94511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94182 q = 1) (hb : d94512 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94182, d94512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94182, d94512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94183 q = 1) (hb : d94513 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94183, d94513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94183, d94513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94184 q = 1) (hb : d94514 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94184, d94514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94184, d94514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94185 q = 1) (hb : d94515 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94185, d94515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94185, d94515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94186 q = 1) (hb : d94516 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94186, d94516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94186, d94516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11693 (p : Pattern) (ha : d77094 p = 1) (hb : d94517 p = 1) : d85158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77089 q = 1) (hb : d83662 q = 1) : d85153 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77089, d85153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9959 q ha hb
    | true =>
      simp only [d77089, d85153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77090 q = 1) (hb : d83662 q = 1) : d85154 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77090, d85154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77090, d85154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77091 q = 1) (hb : d83662 q = 1) : d85155 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77091, d85155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77091, d85155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77092 q = 1) (hb : d83662 q = 1) : d85156 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77092, d85156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77092, d85156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77093 q = 1) (hb : d94517 q = 1) : d85157 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77093, d94517, d85157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77093, d94517, d85157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94517 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d77094 q = 1) (hb : d94517 q = 1) : d85158 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77094, d85158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77094, d85158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11694 (p : Pattern) (ha : d77100 p = 1) (hb : d94517 p = 1) : d85164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94517 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77095 q = 1) (hb : d94517 q = 1) : d85159 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77095, d85159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11693 q ha hb
    | true =>
      simp only [d77095, d85159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77096 q = 1) (hb : d94517 q = 1) : d85160 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77096, d85160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77096, d85160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77097 q = 1) (hb : d94517 q = 1) : d85161 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77097, d85161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77097, d85161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77098 q = 1) (hb : d94517 q = 1) : d85162 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77098, d85162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77098, d85162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77099 q = 1) (hb : d94517 q = 1) : d85163 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77099, d85163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77099, d85163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77100 q = 1) (hb : d94517 q = 1) : d85164 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77100, d85164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77100, d85164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11695 (p : Pattern) (ha : d77106 p = 1) (hb : d94517 p = 1) : d85170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94517 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77101 q = 1) (hb : d94517 q = 1) : d85165 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77101, d85165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11694 q ha hb
    | true =>
      simp only [d77101, d85165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77102 q = 1) (hb : d94517 q = 1) : d85166 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77102, d85166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77102, d85166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77103 q = 1) (hb : d94517 q = 1) : d85167 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77103, d85167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77103, d85167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77104 q = 1) (hb : d94517 q = 1) : d85168 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77104, d85168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77104, d85168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77105 q = 1) (hb : d94517 q = 1) : d85169 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77105, d85169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77105, d85169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77106 q = 1) (hb : d94517 q = 1) : d85170 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77106, d85170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77106, d85170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11696 (p : Pattern) (ha : d77112 p = 1) (hb : d94517 p = 1) : d85176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94517 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77107 q = 1) (hb : d94517 q = 1) : d85171 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77107, d85171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11695 q ha hb
    | true =>
      simp only [d77107, d85171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77108 q = 1) (hb : d94517 q = 1) : d85172 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77108, d85172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77108, d85172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77109 q = 1) (hb : d94517 q = 1) : d85173 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77109, d85173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77109, d85173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77110 q = 1) (hb : d94517 q = 1) : d85174 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77110, d85174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77110, d85174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77111 q = 1) (hb : d94517 q = 1) : d85175 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77111, d85175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77111, d85175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77112 q = 1) (hb : d94517 q = 1) : d85176 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77112, d85176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77112, d85176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11697 (p : Pattern) (ha : d7241 p = 1) (hb : d52001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d148 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7240 q = 1) (hb : d52000 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7240, d52000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7240, d52000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7241 q = 1) (hb : d52001 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7241, d52001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7241, d52001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11698 (p : Pattern) (ha : d7347 p = 1) (hb : d52007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7345 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7345, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7346 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7346, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7347 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7347, d52007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7347, d52007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11699 (p : Pattern) (ha : d52013 p = 1) (hb : d84548 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d52008 q = 1) (hb : d84543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52008, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11698 q hb ha
    | true =>
      simp only [d52008, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d84544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52009, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d84545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d84546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d84547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52013 q = 1) (hb : d84548 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52013, d84548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52013, d84548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro11700 (p : Pattern) (ha : d7368 p = 1) (hb : d52023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7345 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7345, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7346 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7346, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7368 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7368, d52023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7368, d52023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11701 (p : Pattern) (ha : d52029 p = 1) (hb : d84554 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d52008 q = 1) (hb : d84543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52008, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11698 q hb ha
    | true =>
      simp only [d52008, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d84544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52009, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d84545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d84546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d84547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d52024 q = 1) (hb : d84549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52024, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11700 q hb ha
    | true =>
      simp only [d52024, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52025 q = 1) (hb : d84550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d52025, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d52026 q = 1) (hb : d84551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d52026, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d52027 q = 1) (hb : d84552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52027, d84552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d52027, d84552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d52028 q = 1) (hb : d84553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52028, d84553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d52028, d84553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d52029 q = 1) (hb : d84554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52029, d84554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52029, d84554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro11702 (p : Pattern) (ha : d52038 p = 1) (hb : d84561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52024 q = 1) (hb : d84549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52024, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11700 q hb ha
    | true =>
      simp only [d52024, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52025 q = 1) (hb : d84550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52025, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d52026 q = 1) (hb : d84551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52026, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52036 q = 1) (hb : d84559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52036, d84559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52036, d84559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52037 q = 1) (hb : d84560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52037, d84560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52037, d84560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52038 q = 1) (hb : d84561 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52038, d84561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52038, d84561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11703 (p : Pattern) (ha : d7274 p = 1) (hb : d52055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7273 q = 1) (hb : d52054 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7273, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7273, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7274 q = 1) (hb : d52055 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7274, d52055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7274, d52055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11704 (p : Pattern) (ha : d7411 p = 1) (hb : d52061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11703 q ha hb
    | true =>
      simp only [d7275, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7408 q = 1) (hb : d52058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7408, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7408, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7409 q = 1) (hb : d52059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7409, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7409, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7410 q = 1) (hb : d52060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7410, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7410, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7411 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7411, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7411, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11705 (p : Pattern) (ha : d52067 p = 1) (hb : d84572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52062 q = 1) (hb : d84567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52062, d84567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11704 q hb ha
    | true =>
      simp only [d52062, d84567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52063 q = 1) (hb : d84568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52063, d84568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52063, d84568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d52064 q = 1) (hb : d84569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52064, d84569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52064, d84569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52065 q = 1) (hb : d84570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52065, d84570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52065, d84570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52066 q = 1) (hb : d84571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52066, d84571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52066, d84571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52067 q = 1) (hb : d84572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52067, d84572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52067, d84572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11706 (p : Pattern) (ha : d52073 p = 1) (hb : d84578 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d52030 q = 1) (hb : d84555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d84555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11699 q ha hb
    | true =>
      simp only [d52030, d84555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11701 q ha hb
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
  have h8 (q : Pattern) (ha : d52033 q = 1) (hb : d84556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d84556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52033, d84556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52034 q = 1) (hb : d84557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d84557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52034, d84557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52035 q = 1) (hb : d84558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d84558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d84558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52039 q = 1) (hb : d84562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52039, d84562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52039, d84562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11702 q ha hb
  have h12 (q : Pattern) (ha : d52040 q = 1) (hb : d84563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52040, d84563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52040, d84563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52041 q = 1) (hb : d84564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52041, d84564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52041, d84564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d52042 q = 1) (hb : d84565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52042, d84565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52042, d84565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d52043 q = 1) (hb : d84566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d84566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52043, d84566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52068 q = 1) (hb : d84573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52068, d84573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52068, d84573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11705 q ha hb
  have h17 (q : Pattern) (ha : d52069 q = 1) (hb : d84574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52069, d84574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52069, d84574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d52070 q = 1) (hb : d84575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52070, d84575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52070, d84575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d52071 q = 1) (hb : d84576 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52071, d84576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d52071, d84576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d52072 q = 1) (hb : d84577 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52072, d84577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d52072, d84577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d52073 q = 1) (hb : d84578 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d84578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52073, d84578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro11707 (p : Pattern) (ha : d52083 p = 1) (hb : d84588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52008 q = 1) (hb : d84543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52008, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11698 q hb ha
    | true =>
      simp only [d52008, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d52079 q = 1) (hb : d84584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52079, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52079, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52080 q = 1) (hb : d84585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52080, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52080, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52081 q = 1) (hb : d84586 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52081, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52081, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52082 q = 1) (hb : d84587 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52082, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52082, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52083 q = 1) (hb : d84588 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52083, d84588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52083, d84588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11708 (p : Pattern) (ha : d52090 p = 1) (hb : d84595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52008 q = 1) (hb : d84543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52008, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11698 q hb ha
    | true =>
      simp only [d52008, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d52079 q = 1) (hb : d84584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52079, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52079, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52080 q = 1) (hb : d84585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52080, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52080, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52081 q = 1) (hb : d84586 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52081, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52081, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52082 q = 1) (hb : d84587 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52082, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52082, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52024 q = 1) (hb : d84549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52024, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11700 q hb ha
    | true =>
      simp only [d52024, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d52086 q = 1) (hb : d84591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52086, d84591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52086, d84591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52087 q = 1) (hb : d84592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52087, d84592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52087, d84592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52088 q = 1) (hb : d84593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52088, d84593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52088, d84593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52089 q = 1) (hb : d84594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52089, d84594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52089, d84594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52090 q = 1) (hb : d84595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52090, d84595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52090, d84595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro11709 (p : Pattern) (ha : d52163 p = 1) (hb : d84633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52008 q = 1) (hb : d84543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52008, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11698 q hb ha
    | true =>
      simp only [d52008, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d52079 q = 1) (hb : d84584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52079, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52079, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52080 q = 1) (hb : d84585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52080, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52080, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52081 q = 1) (hb : d84586 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52081, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52081, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52082 q = 1) (hb : d84587 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52082, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52082, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d52163 q = 1) (hb : d84633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52163, d84633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52163, d84633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro11710 (p : Pattern) (ha : d7347 p = 1) (hb : d68835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d68834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7347 q = 1) (hb : d68835 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7347, d68835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7347, d68835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11711 (p : Pattern) (ha : d7326 p = 1) (hb : d52129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d328 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d328, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7325 q = 1) (hb : d52128 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7325, d52128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7325, d52128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7326 q = 1) (hb : d52129 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7326, d52129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7326, d52129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11712 (p : Pattern) (ha : d7486 p = 1) (hb : d52135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11711 q ha hb
    | true =>
      simp only [d7327, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d52132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7484 q = 1) (hb : d52133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7484, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7485 q = 1) (hb : d52134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7485, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7486 q = 1) (hb : d52135 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, d52135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7486, d52135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11713 (p : Pattern) (ha : d52095 p = 1) (hb : d84600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7345 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7345, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52094 q = 1) (hb : d84599 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52094, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52094, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52095 q = 1) (hb : d84600 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52095, d84600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52095, d84600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11714 (p : Pattern) (ha : d52102 p = 1) (hb : d84607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52100 q = 1) (hb : d84605 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52100, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52100, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52101 q = 1) (hb : d84606 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52101, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52101, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52102 q = 1) (hb : d84607 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52102, d84607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52102, d84607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11715 (p : Pattern) (ha : d74080 p = 1) (hb : d84616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52096 q = 1) (hb : d84601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52096, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11713 q ha hb
    | true =>
      simp only [d52096, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d52097 q = 1) (hb : d84602 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52097, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52097, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52098 q = 1) (hb : d84603 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52098, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52098, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52099 q = 1) (hb : d84604 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52099, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52099, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52103 q = 1) (hb : d84608 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52103, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11714 q ha hb
    | true =>
      simp only [d52103, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d52104 q = 1) (hb : d84609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52104, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52104, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52105 q = 1) (hb : d84610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52105, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52105, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52136 q = 1) (hb : d84611 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52136, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11712 q hb ha
    | true =>
      simp only [d52136, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11698 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52137 q = 1) (hb : d84612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52137, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52137, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7348 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11710 q ha hb
    | true =>
      simp only [d7348, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7349 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7349, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74077 q = 1) (hb : d84613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74077, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74077, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74078 q = 1) (hb : d84614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74078, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74078, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74079 q = 1) (hb : d84615 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74079, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74079, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74080 q = 1) (hb : d84616 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74080, d84616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74080, d84616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro11716 (p : Pattern) (ha : d7368 p = 1) (hb : d74081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d68834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7368 q = 1) (hb : d74081 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7368, d74081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7368, d74081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11717 (p : Pattern) (ha : d7507 p = 1) (hb : d52153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11711 q ha hb
    | true =>
      simp only [d7327, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d52132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7484 q = 1) (hb : d52133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7484, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7485 q = 1) (hb : d52134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7485, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7507 q = 1) (hb : d52153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, d52153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7507, d52153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11718 (p : Pattern) (ha : d52144 p = 1) (hb : d84617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7345 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7345, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52094 q = 1) (hb : d84599 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52094, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52094, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52144 q = 1) (hb : d84617 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52144, d84617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52144, d84617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11719 (p : Pattern) (ha : d52149 p = 1) (hb : d84622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52100 q = 1) (hb : d84605 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52100, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52100, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52101 q = 1) (hb : d84606 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52101, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52101, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52149 q = 1) (hb : d84622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52149, d84622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52149, d84622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11720 (p : Pattern) (ha : d74087 p = 1) (hb : d84631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52096 q = 1) (hb : d84601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52096, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11713 q ha hb
    | true =>
      simp only [d52096, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d52097 q = 1) (hb : d84602 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52097, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52097, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52098 q = 1) (hb : d84603 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52098, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52098, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52099 q = 1) (hb : d84604 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52099, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52099, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52103 q = 1) (hb : d84608 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52103, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11714 q ha hb
    | true =>
      simp only [d52103, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d52104 q = 1) (hb : d84609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52104, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52104, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52105 q = 1) (hb : d84610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52105, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52105, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52136 q = 1) (hb : d84611 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52136, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11712 q hb ha
    | true =>
      simp only [d52136, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11698 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52137 q = 1) (hb : d84612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52137, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52137, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7348 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11710 q ha hb
    | true =>
      simp only [d7348, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7349 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7349, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74077 q = 1) (hb : d84613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74077, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74077, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74078 q = 1) (hb : d84614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74078, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74078, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74079 q = 1) (hb : d84615 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74079, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74079, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52145 q = 1) (hb : d84618 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52145, d84618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11718 q ha hb
    | true =>
      simp only [d52145, d84618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d52146 q = 1) (hb : d84619 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52146, d84619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52146, d84619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d52147 q = 1) (hb : d84620 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52147, d84620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52147, d84620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d52148 q = 1) (hb : d84621 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52148, d84621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52148, d84621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d52150 q = 1) (hb : d84623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52150, d84623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11719 q ha hb
    | true =>
      simp only [d52150, d84623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d52151 q = 1) (hb : d84624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52151, d84624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52151, d84624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d52152 q = 1) (hb : d84625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52152, d84625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d52152, d84625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d52154 q = 1) (hb : d84626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52154, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11717 q hb ha
    | true =>
      simp only [d52154, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11700 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52155 q = 1) (hb : d84627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52155, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d52155, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7369 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11716 q ha hb
    | true =>
      simp only [d7369, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7370 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7370, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74084 q = 1) (hb : d84628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74084, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74084, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74085 q = 1) (hb : d84629 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74085, d84629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d74085, d84629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74086 q = 1) (hb : d84630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74086, d84630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74086, d84630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74087 q = 1) (hb : d84631 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74087, d84631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74087, d84631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro11721 (p : Pattern) (ha : d74094 p = 1) (hb : d84640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52154 q = 1) (hb : d84626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52154, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11717 q hb ha
    | true =>
      simp only [d52154, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11700 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52155 q = 1) (hb : d84627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52155, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52155, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7369 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11716 q ha hb
    | true =>
      simp only [d7369, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7370 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7370, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74084 q = 1) (hb : d84628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74084, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74084, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74092 q = 1) (hb : d84638 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74092, d84638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74092, d84638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74093 q = 1) (hb : d84639 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74093, d84639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74093, d84639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74094 q = 1) (hb : d84640 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74094, d84640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74094, d84640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11722 (p : Pattern) (ha : d7411 p = 1) (hb : d74103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11703 q ha hb
    | true =>
      simp only [d7275, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7408 q = 1) (hb : d74100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7408, d74100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7408, d74100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7409 q = 1) (hb : d74101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7409, d74101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7409, d74101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7410 q = 1) (hb : d74102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7410, d74102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7410, d74102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7411 q = 1) (hb : d74103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7411, d74103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7411, d74103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11723 (p : Pattern) (ha : d7390 p = 1) (hb : d52189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d421 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7389 q = 1) (hb : d52188 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7389, d52188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7389, d52188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7390 q = 1) (hb : d52189 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7390, d52189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7390, d52189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11724 (p : Pattern) (ha : d7554 p = 1) (hb : d52195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d52190 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d52190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11723 q ha hb
    | true =>
      simp only [d7391, d52190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d52191 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d52191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d52191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7551 q = 1) (hb : d52192 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7551, d52192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7551, d52192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7552 q = 1) (hb : d52193 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7552, d52193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7552, d52193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7553 q = 1) (hb : d52194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7553, d52194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7553, d52194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7554 q = 1) (hb : d52195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7554, d52195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7554, d52195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11725 (p : Pattern) (ha : d74109 p = 1) (hb : d84651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52196 q = 1) (hb : d84646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52196, d84646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11724 q hb ha
    | true =>
      simp only [d52196, d84646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11704 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52197 q = 1) (hb : d84647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52197, d84647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52197, d84647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7412 q = 1) (hb : d74104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7412, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11722 q ha hb
    | true =>
      simp only [d7412, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7413 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7413, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7413, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74106 q = 1) (hb : d84648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74106, d84648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74106, d84648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74107 q = 1) (hb : d84649 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74107, d84649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74107, d84649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74108 q = 1) (hb : d84650 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74108, d84650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74108, d84650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74109 q = 1) (hb : d84651 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74109, d84651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74109, d84651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11726 (p : Pattern) (ha : d74115 p = 1) (hb : d84657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52084 q = 1) (hb : d84589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52084, d84589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52084, d84589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11707 q ha hb
  have h2 (q : Pattern) (ha : d52085 q = 1) (hb : d84590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52085, d84590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52085, d84590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d52091 q = 1) (hb : d84596 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52091, d84596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11707 q ha hb
    | true =>
      simp only [d52091, d84596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11708 q ha hb
  have h4 (q : Pattern) (ha : d52092 q = 1) (hb : d84597 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52092, d84597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52092, d84597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52093 q = 1) (hb : d84598 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52093, d84598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52093, d84598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74088 q = 1) (hb : d84632 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74088, d84632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11715 q ha hb
    | true =>
      simp only [d74088, d84632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11720 q ha hb
  have h7 (q : Pattern) (ha : d52164 q = 1) (hb : d84634 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52164, d84634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11709 q ha hb
    | true =>
      simp only [d52164, d84634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d74089 q = 1) (hb : d84635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74089, d84635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74089, d84635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74090 q = 1) (hb : d84636 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74090, d84636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74090, d84636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74091 q = 1) (hb : d84637 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74091, d84637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74091, d84637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74095 q = 1) (hb : d84641 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74095, d84641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74095, d84641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11721 q ha hb
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
  have h13 (q : Pattern) (ha : d74096 q = 1) (hb : d84642 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74096, d84642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74096, d84642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74097 q = 1) (hb : d84643 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74097, d84643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74097, d84643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74098 q = 1) (hb : d84644 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74098, d84644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74098, d84644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74099 q = 1) (hb : d84645 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74099, d84645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74099, d84645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74110 q = 1) (hb : d84652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74110, d84652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74110, d84652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11725 q ha hb
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
  have h19 (q : Pattern) (ha : d74111 q = 1) (hb : d84653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74111, d84653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74111, d84653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74112 q = 1) (hb : d84654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74112, d84654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74112, d84654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74113 q = 1) (hb : d84655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74113, d84655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74113, d84655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74114 q = 1) (hb : d84656 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74114, d84656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74114, d84656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74115 q = 1) (hb : d84657 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74115, d84657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74115, d84657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11727 (p : Pattern) (ha : d74121 p = 1) (hb : d84663 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d52074 q = 1) (hb : d84579 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d84579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52074, d84579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11706 q ha hb
  have h6 (q : Pattern) (ha : d52075 q = 1) (hb : d84580 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d84580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52075, d84580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52076 q = 1) (hb : d84581 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d84581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52076, d84581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52077 q = 1) (hb : d84582 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d84582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52077, d84582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52078 q = 1) (hb : d84583 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d84583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52078, d84583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74116 q = 1) (hb : d84658 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74116, d84658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74116, d84658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11726 q ha hb
  have h11 (q : Pattern) (ha : d74117 q = 1) (hb : d84659 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74117, d84659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74117, d84659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74118 q = 1) (hb : d84660 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74118, d84660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74118, d84660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74119 q = 1) (hb : d84661 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74119, d84661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74119, d84661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74120 q = 1) (hb : d84662 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74120, d84662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74120, d84662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74121 q = 1) (hb : d84663 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74121, d84663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74121, d84663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11728 (p : Pattern) (ha : d7326 p = 1) (hb : d52224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d328 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d328, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7325 q = 1) (hb : d52223 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7325, d52223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7325, d52223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7326 q = 1) (hb : d52224 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7326, d52224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7326, d52224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11729 (p : Pattern) (ha : d7486 p = 1) (hb : d52234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7484 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7484, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7485 q = 1) (hb : d52233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7485, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7486 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, d52234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7486, d52234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11730 (p : Pattern) (ha : d52244 p = 1) (hb : d84669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52239 q = 1) (hb : d84664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52239, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11729 q hb ha
    | true =>
      simp only [d52239, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d52240 q = 1) (hb : d84665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52240, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52240, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52241 q = 1) (hb : d84666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52241, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52241, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52242 q = 1) (hb : d84667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52242, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52242, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52243 q = 1) (hb : d84668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52243, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52243, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52244 q = 1) (hb : d84669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52244, d84669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52244, d84669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11731 (p : Pattern) (ha : d7507 p = 1) (hb : d52247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7484 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7484, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7485 q = 1) (hb : d52233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7485, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7507 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, d52247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7507, d52247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11732 (p : Pattern) (ha : d52254 p = 1) (hb : d84677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52239 q = 1) (hb : d84664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52239, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11729 q hb ha
    | true =>
      simp only [d52239, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d52240 q = 1) (hb : d84665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52240, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52240, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52241 q = 1) (hb : d84666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52241, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52241, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52242 q = 1) (hb : d84667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52242, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52242, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52243 q = 1) (hb : d84668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52243, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52243, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52249 q = 1) (hb : d84672 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52249, d84672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11731 q hb ha
    | true =>
      simp only [d52249, d84672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h7 (q : Pattern) (ha : d52250 q = 1) (hb : d84673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52250, d84673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52250, d84673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52251 q = 1) (hb : d84674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52251, d84674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52251, d84674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52252 q = 1) (hb : d84675 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52252, d84675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52252, d84675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52253 q = 1) (hb : d84676 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52253, d84676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52253, d84676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52254 q = 1) (hb : d84677 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52254, d84677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52254, d84677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro11733 (p : Pattern) (ha : d52342 p = 1) (hb : d84720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52239 q = 1) (hb : d84664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52239, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11729 q hb ha
    | true =>
      simp only [d52239, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d52240 q = 1) (hb : d84665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52240, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52240, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52241 q = 1) (hb : d84666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52241, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52241, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52242 q = 1) (hb : d84667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52242, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52242, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52243 q = 1) (hb : d84668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52243, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52243, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d52342 q = 1) (hb : d84720 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52342, d84720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52342, d84720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro11734 (p : Pattern) (ha : d7486 p = 1) (hb : d74125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7483 q = 1) (hb : d74122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d74123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7484, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d74124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d74124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, d74124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7486 q = 1) (hb : d74125 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, d74125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7486, d74125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11735 (p : Pattern) (ha : d52259 p = 1) (hb : d84682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7484 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7484, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52258 q = 1) (hb : d84681 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52258, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52258, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52259 q = 1) (hb : d84682 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52259, d84682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52259, d84682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11736 (p : Pattern) (ha : d52268 p = 1) (hb : d84689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52266 q = 1) (hb : d84687 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52266, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52266, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52267 q = 1) (hb : d84688 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52267, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52267, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52268 q = 1) (hb : d84689 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52268, d84689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52268, d84689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11737 (p : Pattern) (ha : d7465 p = 1) (hb : d52301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d549 q = 1) (hb : d52296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77 q ha hb
    | true =>
      simp only [d549, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
  have h2 (q : Pattern) (ha : d550 q = 1) (hb : d52297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d551 q = 1) (hb : d52298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d325 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h5 (q : Pattern) (ha : d326 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d327 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d552 q = 1) (hb : d52299 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d552, d52299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d552, d52299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7464 q = 1) (hb : d52300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7464, d52300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7464, d52300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7465 q = 1) (hb : d52301 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7465, d52301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7465, d52301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11738 (p : Pattern) (ha : d52307 p = 1) (hb : d84696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d52302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11737 q ha hb
    | true =>
      simp only [d7466, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d52303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52304 q = 1) (hb : d84693 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52304, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52304, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d52305 q = 1) (hb : d84694 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52305, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52305, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52306 q = 1) (hb : d84695 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52306, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52306, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52307 q = 1) (hb : d84696 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52307, d84696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52307, d84696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11739 (p : Pattern) (ha : d74131 p = 1) (hb : d84702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52262 q = 1) (hb : d84683 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52262, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11735 q ha hb
    | true =>
      simp only [d52262, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q hb ha
  have h2 (q : Pattern) (ha : d52263 q = 1) (hb : d84684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52263, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52263, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52264 q = 1) (hb : d84685 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52264, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52264, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52265 q = 1) (hb : d84686 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52265, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52265, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52272 q = 1) (hb : d84690 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52272, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11736 q ha hb
    | true =>
      simp only [d52272, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q hb ha
  have h6 (q : Pattern) (ha : d52273 q = 1) (hb : d84691 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52273, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52273, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52274 q = 1) (hb : d84692 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52274, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52274, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52308 q = 1) (hb : d84697 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52308, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11738 q ha hb
    | true =>
      simp only [d52308, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11729 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52309 q = 1) (hb : d84698 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52309, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52309, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7487 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11734 q ha hb
    | true =>
      simp only [d7487, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7488 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7488, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74128 q = 1) (hb : d84699 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74128, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74128, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74129 q = 1) (hb : d84700 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74129, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74129, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74130 q = 1) (hb : d84701 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74130, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74130, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74131 q = 1) (hb : d84702 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74131, d84702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74131, d84702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro11740 (p : Pattern) (ha : d7507 p = 1) (hb : d74132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7483 q = 1) (hb : d74122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d74122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d74123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7484, d74123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d74124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d74124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, d74124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7507 q = 1) (hb : d74132 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, d74132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7507, d74132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11741 (p : Pattern) (ha : d52316 p = 1) (hb : d84703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7484 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7484, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52258 q = 1) (hb : d84681 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52258, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52258, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52316 q = 1) (hb : d84703 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52316, d84703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52316, d84703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11742 (p : Pattern) (ha : d52322 p = 1) (hb : d84708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52266 q = 1) (hb : d84687 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52266, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52266, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52267 q = 1) (hb : d84688 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52267, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52267, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52322 q = 1) (hb : d84708 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52322, d84708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52322, d84708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11743 (p : Pattern) (ha : d52327 p = 1) (hb : d84712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d52302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11737 q ha hb
    | true =>
      simp only [d7466, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d52303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52304 q = 1) (hb : d84693 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52304, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52304, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d52305 q = 1) (hb : d84694 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52305, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52305, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52306 q = 1) (hb : d84695 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52306, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52306, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52327 q = 1) (hb : d84712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52327, d84712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52327, d84712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11744 (p : Pattern) (ha : d74138 p = 1) (hb : d84718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52262 q = 1) (hb : d84683 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52262, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11735 q ha hb
    | true =>
      simp only [d52262, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q hb ha
  have h2 (q : Pattern) (ha : d52263 q = 1) (hb : d84684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52263, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52263, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52264 q = 1) (hb : d84685 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52264, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52264, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52265 q = 1) (hb : d84686 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52265, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52265, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52272 q = 1) (hb : d84690 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52272, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11736 q ha hb
    | true =>
      simp only [d52272, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q hb ha
  have h6 (q : Pattern) (ha : d52273 q = 1) (hb : d84691 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52273, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52273, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52274 q = 1) (hb : d84692 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52274, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52274, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52308 q = 1) (hb : d84697 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52308, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11738 q ha hb
    | true =>
      simp only [d52308, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11729 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52309 q = 1) (hb : d84698 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52309, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52309, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7487 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11734 q ha hb
    | true =>
      simp only [d7487, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7488 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7488, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74128 q = 1) (hb : d84699 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74128, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74128, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74129 q = 1) (hb : d84700 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74129, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74129, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74130 q = 1) (hb : d84701 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74130, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74130, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52318 q = 1) (hb : d84704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52318, d84704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11741 q ha hb
    | true =>
      simp only [d52318, d84704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94 q hb ha
  have h17 (q : Pattern) (ha : d52319 q = 1) (hb : d84705 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52319, d84705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52319, d84705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d52320 q = 1) (hb : d84706 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52320, d84706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52320, d84706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d52321 q = 1) (hb : d84707 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52321, d84707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52321, d84707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d52324 q = 1) (hb : d84709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52324, d84709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11742 q ha hb
    | true =>
      simp only [d52324, d84709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q hb ha
  have h21 (q : Pattern) (ha : d52325 q = 1) (hb : d84710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52325, d84710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52325, d84710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d52326 q = 1) (hb : d84711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52326, d84711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d52326, d84711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d52328 q = 1) (hb : d84713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52328, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11743 q ha hb
    | true =>
      simp only [d52328, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11731 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52329 q = 1) (hb : d84714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52329, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d52329, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7508 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11740 q ha hb
    | true =>
      simp only [d7508, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7509 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7509, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74135 q = 1) (hb : d84715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74135, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74135, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74136 q = 1) (hb : d84716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74136, d84716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d74136, d84716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74137 q = 1) (hb : d84717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74137, d84717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74137, d84717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74138 q = 1) (hb : d84718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74138, d84718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74138, d84718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro11745 (p : Pattern) (ha : d74145 p = 1) (hb : d84727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52328 q = 1) (hb : d84713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52328, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11743 q ha hb
    | true =>
      simp only [d52328, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11731 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52329 q = 1) (hb : d84714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52329, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52329, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7508 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11740 q ha hb
    | true =>
      simp only [d7508, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7509 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7509, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74135 q = 1) (hb : d84715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74135, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74135, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74143 q = 1) (hb : d84725 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74143, d84725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74143, d84725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74144 q = 1) (hb : d84726 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74144, d84726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74144, d84726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74145 q = 1) (hb : d84727 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74145, d84727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74145, d84727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11746 (p : Pattern) (ha : d7390 p = 1) (hb : d52379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d421 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7389 q = 1) (hb : d52378 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7389, d52378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7389, d52378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7390 q = 1) (hb : d52379 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7390, d52379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7390, d52379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11747 (p : Pattern) (ha : d7554 p = 1) (hb : d52393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d52380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11746 q ha hb
    | true =>
      simp only [d7391, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7551 q = 1) (hb : d52390 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7551, d52390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7551, d52390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7552 q = 1) (hb : d52391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7552, d52391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7552, d52391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7553 q = 1) (hb : d52392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7553, d52392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7553, d52392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7554 q = 1) (hb : d52393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7554, d52393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7554, d52393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11748 (p : Pattern) (ha : d7554 p = 1) (hb : d74154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d52380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11746 q ha hb
    | true =>
      simp only [d7391, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7551 q = 1) (hb : d74151 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7551, d74151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7551, d74151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7552 q = 1) (hb : d74152 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7552, d74152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7552, d74152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7553 q = 1) (hb : d74153 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7553, d74153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7553, d74153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7554 q = 1) (hb : d74154 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7554, d74154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7554, d74154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11749 (p : Pattern) (ha : d7529 p = 1) (hb : d52374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d665 q = 1) (hb : d52369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81 q ha hb
    | true =>
      simp only [d665, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
  have h2 (q : Pattern) (ha : d666 q = 1) (hb : d52370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d667 q = 1) (hb : d52371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d418 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h5 (q : Pattern) (ha : d419 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d420 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d668 q = 1) (hb : d52372 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d668, d52372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d668, d52372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7528 q = 1) (hb : d52373 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7528, d52373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7528, d52373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7529 q = 1) (hb : d52374 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7529, d52374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7529, d52374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
end NetHack.Soko22Hazard87
