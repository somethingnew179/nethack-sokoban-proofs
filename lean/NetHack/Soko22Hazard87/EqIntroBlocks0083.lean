import NetHack.Soko22Hazard87.EqIntroBlocks0082
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro20750 (p : Pattern) (selected : d213179 p = 0) : d215034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d212963 q = 0) : d214868 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212963, d214868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d212963, d214868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20702 q selected
  have h2 (q : Pattern) (selected : d212964 q = 0) : d214869 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212964, d214869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d212964, d214869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d212973 q = 0) : d214878 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212973, d214878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20702 q selected
    | true =>
      simp only [d212973, d214878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20705 q selected
  have h4 (q : Pattern) (selected : d212974 q = 0) : d214879 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212974, d214879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212974, d214879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d212975 q = 0) : d214880 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212975, d214880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d212975, d214880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213070 q = 0) : d214948 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213070, d214948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20720 q selected
    | true =>
      simp only [d213070, d214948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20729 q selected
  have h7 (q : Pattern) (selected : d213083 q = 0) : d214961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213083, d214961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20730 q selected
    | true =>
      simp only [d213083, d214961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20731 q selected
  have h8 (q : Pattern) (selected : d213084 q = 0) : d214962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213084, d214962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213084, d214962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213085 q = 0) : d214963 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213085, d214963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213085, d214963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d213086 q = 0) : d214964 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213086, d214964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213086, d214964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213090 q = 0) : d214968 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213090, d214968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213090, d214968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20732 q selected
  have h12 (q : Pattern) (selected : d213092 q = 0) : d214970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213092, d214970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213092, d214970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20733 q selected
  have h13 (q : Pattern) (selected : d213093 q = 0) : d214971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213093, d214971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213093, d214971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213094 q = 0) : d214972 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213094, d214972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d213094, d214972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d213095 q = 0) : d214973 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213095, d214973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d213095, d214973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d213096 q = 0) : d214974 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213096, d214974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213096, d214974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d213163 q = 0) : d215022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213163, d215022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213163, d215022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20747 q selected
  have h18 (q : Pattern) (selected : d213174 q = 0) : d215029 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213174, d215029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213174, d215029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20749 q selected
  have h19 (q : Pattern) (selected : d213175 q = 0) : d215030 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213175, d215030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d213175, d215030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d213176 q = 0) : d215031 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213176, d215031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d213176, d215031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d213177 q = 0) : d215032 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213177, d215032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d213177, d215032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d213178 q = 0) : d215033 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213178, d215033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d213178, d215033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d213179 q = 0) : d215034 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d213179, d215034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213179, d215034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20751 (p : Pattern) (selected : d213185 p = 0) : d215040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213180 q = 0) : d215035 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d213180, d215035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213180, d215035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20750 q selected
  have h2 (q : Pattern) (selected : d213181 q = 0) : d215036 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d213181, d215036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213181, d215036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213182 q = 0) : d215037 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d213182, d215037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213182, d215037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213183 q = 0) : d215038 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d213183, d215038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213183, d215038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213184 q = 0) : d215039 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d213184, d215039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213184, d215039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213185 q = 0) : d215040 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d213185, d215040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213185, d215040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20752 (p : Pattern) (selected : d213188 p = 0) : d215043 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d543 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d544 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d545 q = 0) : d52292 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9458 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9460 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16073 q = 0) : d126981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d126981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16073, d126981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d212993 q = 0) : d214898 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d212993, d214898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d212993, d214898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d12748 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d753 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213187 q = 0) : d215042 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213187, d215042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213187, d215042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213188 q = 0) : d215043 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213188, d215043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213188, d215043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20753 (p : Pattern) (selected : d213191 p = 0) : d215046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d319 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d320 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d321 q = 0) : d52120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d753 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213189 q = 0) : d215044 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213189, d215044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213189, d215044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213190 q = 0) : d215045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213190, d215045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213190, d215045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213191 q = 0) : d215046 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213191, d215046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213191, d215046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20754 (p : Pattern) (selected : d213194 p = 0) : d215049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d753 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213190 q = 0) : d215045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213190, d215045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213190, d215045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213194 q = 0) : d215049 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213194, d215049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213194, d215049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20755 (p : Pattern) (selected : d213200 p = 0) : d215055 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213192 q = 0) : d215047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213192, d215047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20752 q selected
    | true =>
      simp only [d213192, d215047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20753 q selected
  have h2 (q : Pattern) (selected : d213193 q = 0) : d215048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213193, d215048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213193, d215048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213195 q = 0) : d215050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213195, d215050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20753 q selected
    | true =>
      simp only [d213195, d215050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20754 q selected
  have h4 (q : Pattern) (selected : d213196 q = 0) : d215051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213196, d215051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213196, d215051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213197 q = 0) : d215052 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213197, d215052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213197, d215052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213198 q = 0) : d215053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213198, d215053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213198, d215053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213199 q = 0) : d215054 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213199, d215054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213199, d215054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213200 q = 0) : d215055 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213200, d215055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213200, d215055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20756 (p : Pattern) (selected : d213204 p = 0) : d215059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213195 q = 0) : d215050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213195, d215050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20753 q selected
    | true =>
      simp only [d213195, d215050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20754 q selected
  have h2 (q : Pattern) (selected : d213196 q = 0) : d215051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213196, d215051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213196, d215051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213198 q = 0) : d215053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213198, d215053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213198, d215053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213203 q = 0) : d215058 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213203, d215058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213203, d215058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213204 q = 0) : d215059 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213204, d215059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213204, d215059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20757 (p : Pattern) (selected : d213210 p = 0) : d215065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213201 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20755 q selected
    | true =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213202 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213207 q = 0) : d215062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213208 q = 0) : d215063 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213208, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213208, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213209 q = 0) : d215064 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213209, d215064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213209, d215064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213210 q = 0) : d215065 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213210, d215065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213210, d215065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20758 (p : Pattern) (selected : d213214 p = 0) : d215069 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213211 q = 0) : d215066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213212 q = 0) : d215067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213212, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213212, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213213 q = 0) : d215068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213213, d215068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213213, d215068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213214 q = 0) : d215069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213214, d215069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213214, d215069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20759 (p : Pattern) (selected : d213220 p = 0) : d215075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213215 q = 0) : d215070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213215, d215070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20757 q selected
    | true =>
      simp only [d213215, d215070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20758 q selected
  have h2 (q : Pattern) (selected : d213216 q = 0) : d215071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213216, d215071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213216, d215071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213217 q = 0) : d215072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213217, d215072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213217, d215072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213218 q = 0) : d215073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213218, d215073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213218, d215073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213219 q = 0) : d215074 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213219, d215074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213219, d215074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213220 q = 0) : d215075 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213220, d215075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213220, d215075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20760 (p : Pattern) (selected : d213223 p = 0) : d215078 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213201 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20755 q selected
    | true =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213202 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213207 q = 0) : d215062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213208 q = 0) : d215063 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213208, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213208, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213209 q = 0) : d215064 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213209, d215064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213209, d215064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213223 q = 0) : d215078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213223, d215078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213223, d215078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20761 (p : Pattern) (selected : d213224 p = 0) : d215079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213211 q = 0) : d215066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213212 q = 0) : d215067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213212, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213212, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213213 q = 0) : d215068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213213, d215068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213213, d215068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213224 q = 0) : d215079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213224, d215079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213224, d215079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20762 (p : Pattern) (selected : d213230 p = 0) : d215085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213215 q = 0) : d215070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213215, d215070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20757 q selected
    | true =>
      simp only [d213215, d215070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20758 q selected
  have h2 (q : Pattern) (selected : d213216 q = 0) : d215071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213216, d215071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213216, d215071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213217 q = 0) : d215072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213217, d215072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213217, d215072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213218 q = 0) : d215073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213218, d215073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213218, d215073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213219 q = 0) : d215074 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213219, d215074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213219, d215074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213225 q = 0) : d215080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213225, d215080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20760 q selected
    | true =>
      simp only [d213225, d215080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20761 q selected
  have h7 (q : Pattern) (selected : d213226 q = 0) : d215081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213226, d215081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213226, d215081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213227 q = 0) : d215082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213227, d215082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213227, d215082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213228 q = 0) : d215083 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213228, d215083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213228, d215083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213229 q = 0) : d215084 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213229, d215084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213229, d215084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213230 q = 0) : d215085 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213230, d215085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213230, d215085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro20763 (p : Pattern) (selected : d213235 p = 0) : d215090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213201 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20755 q selected
    | true =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213202 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213207 q = 0) : d215062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213208 q = 0) : d215063 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213208, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213208, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213234 q = 0) : d215089 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213234, d215089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213234, d215089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213235 q = 0) : d215090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213235, d215090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213235, d215090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20764 (p : Pattern) (selected : d213237 p = 0) : d215092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213211 q = 0) : d215066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213212 q = 0) : d215067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213212, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213212, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213236 q = 0) : d215091 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213236, d215091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213236, d215091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213237 q = 0) : d215092 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213237, d215092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213237, d215092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20765 (p : Pattern) (selected : d213244 p = 0) : d215099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213201 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20755 q selected
    | true =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213202 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213207 q = 0) : d215062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213242 q = 0) : d215097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213242, d215097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213242, d215097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213243 q = 0) : d215098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213243, d215098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213243, d215098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213244 q = 0) : d215099 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213244, d215099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213244, d215099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20766 (p : Pattern) (selected : d213247 p = 0) : d215102 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213211 q = 0) : d215066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213245 q = 0) : d215100 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213245, d215100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213245, d215100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213246 q = 0) : d215101 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213246, d215101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213246, d215101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213247 q = 0) : d215102 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213247, d215102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213247, d215102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20767 (p : Pattern) (selected : d213253 p = 0) : d215108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d834 q = 0) : d52511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d835 q = 0) : d52512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d836 q = 0) : d52513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9587 q = 0) : d101167 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
    | true =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9589 q = 0) : d101169 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16270 q = 0) : d127147 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, d127147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16270, d127147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213251 q = 0) : d215106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213251, d215106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213251, d215106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9597 q = 0) : d101177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9599 q = 0) : d101179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14529 q = 0) : d122766 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, d122766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14529, d122766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d12748 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213252 q = 0) : d215107 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213252, d215107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213252, d215107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213253 q = 0) : d215108 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213253, d215108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213253, d215108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20768 (p : Pattern) (selected : d213256 p = 0) : d215111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12748 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d753 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213187 q = 0) : d215042 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213187, d215042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213187, d215042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213190 q = 0) : d215045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213190, d215045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213190, d215045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213256 q = 0) : d215111 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213256, d215111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213256, d215111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20769 (p : Pattern) (selected : d213261 p = 0) : d215116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213254 q = 0) : d215109 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213254, d215109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20767 q selected
    | true =>
      simp only [d213254, d215109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20752 q selected
  have h2 (q : Pattern) (selected : d213255 q = 0) : d215110 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213255, d215110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213255, d215110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213257 q = 0) : d215112 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213257, d215112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20752 q selected
    | true =>
      simp only [d213257, d215112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20768 q selected
  have h4 (q : Pattern) (selected : d213258 q = 0) : d215113 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213258, d215113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213258, d215113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213259 q = 0) : d215114 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213259, d215114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213259, d215114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213192 q = 0) : d215047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213192, d215047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20752 q selected
    | true =>
      simp only [d213192, d215047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20753 q selected
  have h7 (q : Pattern) (selected : d213193 q = 0) : d215048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213193, d215048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213193, d215048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213195 q = 0) : d215050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213195, d215050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20753 q selected
    | true =>
      simp only [d213195, d215050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20754 q selected
  have h9 (q : Pattern) (selected : d213196 q = 0) : d215051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213196, d215051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213196, d215051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213197 q = 0) : d215052 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213197, d215052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213197, d215052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213260 q = 0) : d215115 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213260, d215115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213260, d215115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213261 q = 0) : d215116 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213261, d215116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213261, d215116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro20770 (p : Pattern) (selected : d213267 p = 0) : d215122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213262 q = 0) : d215117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213262, d215117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20769 q selected
    | true =>
      simp only [d213262, d215117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213263 q = 0) : d215118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213263, d215118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213263, d215118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213201 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20755 q selected
    | true =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213202 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213264 q = 0) : d215119 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213264, d215119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213264, d215119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213265 q = 0) : d215120 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213265, d215120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213265, d215120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213266 q = 0) : d215121 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213266, d215121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213266, d215121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213267 q = 0) : d215122 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213267, d215122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213267, d215122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20771 (p : Pattern) (selected : d213271 p = 0) : d215043 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d868 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
    | true =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d869 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d869, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d869, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d870 q = 0) : d52292 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d870, d52292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d870, d52292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9661 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
    | true =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9663 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9663, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9663, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16292 q = 0) : d126981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16292, d126981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16292, d126981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213269 q = 0) : d214898 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213269, d214898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213269, d214898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9671 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
    | true =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9673 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14551 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14551, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14551, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d876 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213270 q = 0) : d215042 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213270, d215042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213270, d215042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213271 q = 0) : d215043 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213271, d215043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213271, d215043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20772 (p : Pattern) (selected : d213274 p = 0) : d215046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d574 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d576 q = 0) : d52120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d576, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d576, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d876 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213272 q = 0) : d215044 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213272, d215044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213272, d215044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213273 q = 0) : d215045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213273, d215045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213273, d215045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213274 q = 0) : d215046 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213274, d215046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213274, d215046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20773 (p : Pattern) (selected : d213277 p = 0) : d215049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d876 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213273 q = 0) : d215045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213273, d215045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213273, d215045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213277 q = 0) : d215049 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213277, d215049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213277, d215049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20774 (p : Pattern) (selected : d213283 p = 0) : d215055 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213275 q = 0) : d215047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213275, d215047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20771 q selected
    | true =>
      simp only [d213275, d215047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20772 q selected
  have h2 (q : Pattern) (selected : d213276 q = 0) : d215048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213276, d215048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213276, d215048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213278 q = 0) : d215050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213278, d215050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20772 q selected
    | true =>
      simp only [d213278, d215050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20773 q selected
  have h4 (q : Pattern) (selected : d213279 q = 0) : d215051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213279, d215051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213279, d215051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213280 q = 0) : d215052 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213280, d215052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213280, d215052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213281 q = 0) : d215053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213281, d215053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213281, d215053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213282 q = 0) : d215054 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213282, d215054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213282, d215054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213283 q = 0) : d215055 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213283, d215055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213283, d215055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20775 (p : Pattern) (selected : d213287 p = 0) : d215059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213278 q = 0) : d215050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213278, d215050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20772 q selected
    | true =>
      simp only [d213278, d215050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20773 q selected
  have h2 (q : Pattern) (selected : d213279 q = 0) : d215051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213279, d215051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213279, d215051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213281 q = 0) : d215053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213281, d215053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213281, d215053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213286 q = 0) : d215058 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213286, d215058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213286, d215058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213287 q = 0) : d215059 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213287, d215059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213287, d215059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20776 (p : Pattern) (selected : d213293 p = 0) : d215065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213284 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213284, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20774 q selected
    | true =>
      simp only [d213284, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213285 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213285, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213285, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213288 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213288, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20775 q selected
    | true =>
      simp only [d213288, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213289 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213289, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213289, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213290 q = 0) : d215062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213290, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213290, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213291 q = 0) : d215063 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213291, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213291, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213292 q = 0) : d215064 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213292, d215064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213292, d215064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213293 q = 0) : d215065 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213293, d215065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213293, d215065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20777 (p : Pattern) (selected : d213297 p = 0) : d215069 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213288 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213288, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20775 q selected
    | true =>
      simp only [d213288, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213289 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213289, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213289, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213294 q = 0) : d215066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213294, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213294, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213295 q = 0) : d215067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213295, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213295, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213296 q = 0) : d215068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213296, d215068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213296, d215068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213297 q = 0) : d215069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213297, d215069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213297, d215069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20778 (p : Pattern) (selected : d213303 p = 0) : d215128 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213201 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20755 q selected
    | true =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213202 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213300 q = 0) : d215125 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213300, d215125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213300, d215125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213301 q = 0) : d215126 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213301, d215126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213301, d215126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213302 q = 0) : d215127 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213302, d215127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213302, d215127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213303 q = 0) : d215128 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213303, d215128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213303, d215128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20779 (p : Pattern) (selected : d213309 p = 0) : d215134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213238 q = 0) : d215093 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213238, d215093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20763 q selected
    | true =>
      simp only [d213238, d215093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20764 q selected
  have h2 (q : Pattern) (selected : d213239 q = 0) : d215094 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213239, d215094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213239, d215094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213240 q = 0) : d215095 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213240, d215095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213240, d215095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213241 q = 0) : d215096 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213241, d215096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213241, d215096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213248 q = 0) : d215103 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213248, d215103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20765 q selected
    | true =>
      simp only [d213248, d215103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20766 q selected
  have h6 (q : Pattern) (selected : d213249 q = 0) : d215104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213249, d215104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213249, d215104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213250 q = 0) : d215105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213250, d215105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213250, d215105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213268 q = 0) : d215123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213268, d215123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20770 q selected
    | true =>
      simp only [d213268, d215123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20757 q selected
  have h9 (q : Pattern) (selected : d213298 q = 0) : d215070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213298, d215070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20776 q selected
    | true =>
      simp only [d213298, d215070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20777 q selected
  have h10 (q : Pattern) (selected : d213299 q = 0) : d215124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213299, d215124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213299, d215124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213304 q = 0) : d215129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213304, d215129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20778 q selected
    | true =>
      simp only [d213304, d215129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213305 q = 0) : d215130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213305, d215130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213305, d215130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213306 q = 0) : d215131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213306, d215131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213306, d215131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213307 q = 0) : d215132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213307, d215132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213307, d215132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213308 q = 0) : d215133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213308, d215133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213308, d215133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213309 q = 0) : d215134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213309, d215134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213309, d215134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro20780 (p : Pattern) (selected : d213310 p = 0) : d215135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213201 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20755 q selected
    | true =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213202 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213207 q = 0) : d215062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213208 q = 0) : d215063 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213208, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213208, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213234 q = 0) : d215089 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213234, d215089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213234, d215089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213310 q = 0) : d215135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213310, d215135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213310, d215135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20781 (p : Pattern) (selected : d213311 p = 0) : d215136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213211 q = 0) : d215066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213212 q = 0) : d215067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213212, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213212, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213236 q = 0) : d215091 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213236, d215091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213236, d215091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213311 q = 0) : d215136 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213311, d215136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213311, d215136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20782 (p : Pattern) (selected : d213316 p = 0) : d215141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213201 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20755 q selected
    | true =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213202 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213207 q = 0) : d215062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213207, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213242 q = 0) : d215097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213242, d215097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213242, d215097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213243 q = 0) : d215098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213243, d215098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213243, d215098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213316 q = 0) : d215141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213316, d215141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213316, d215141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20783 (p : Pattern) (selected : d213317 p = 0) : d215142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213205 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20756 q selected
    | true =>
      simp only [d213205, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213206 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213206, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213211 q = 0) : d215066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213211, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213245 q = 0) : d215100 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213245, d215100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213245, d215100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213246 q = 0) : d215101 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213246, d215101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213246, d215101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213317 q = 0) : d215142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213317, d215142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213317, d215142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20784 (p : Pattern) (selected : d213321 p = 0) : d215146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213262 q = 0) : d215117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213262, d215117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20769 q selected
    | true =>
      simp only [d213262, d215117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213263 q = 0) : d215118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213263, d215118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213263, d215118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213201 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20755 q selected
    | true =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213202 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213264 q = 0) : d215119 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213264, d215119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213264, d215119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213265 q = 0) : d215120 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213265, d215120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213265, d215120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213266 q = 0) : d215121 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213266, d215121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213266, d215121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213321 q = 0) : d215146 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213321, d215146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213321, d215146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20785 (p : Pattern) (selected : d213323 p = 0) : d215078 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213284 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213284, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20774 q selected
    | true =>
      simp only [d213284, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213285 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213285, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213285, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213288 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213288, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20775 q selected
    | true =>
      simp only [d213288, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213289 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213289, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213289, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213290 q = 0) : d215062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213290, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213290, d215062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213291 q = 0) : d215063 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213291, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213291, d215063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213292 q = 0) : d215064 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213292, d215064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213292, d215064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213323 q = 0) : d215078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213323, d215078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213323, d215078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20786 (p : Pattern) (selected : d213324 p = 0) : d215079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213288 q = 0) : d215060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213288, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20775 q selected
    | true =>
      simp only [d213288, d215060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213289 q = 0) : d215061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213289, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213289, d215061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213294 q = 0) : d215066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213294, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213294, d215066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213295 q = 0) : d215067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213295, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213295, d215067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213296 q = 0) : d215068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213296, d215068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213296, d215068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213324 q = 0) : d215079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213324, d215079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213324, d215079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20787 (p : Pattern) (selected : d213327 p = 0) : d215149 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213201 q = 0) : d215056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20755 q selected
    | true =>
      simp only [d213201, d215056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213202 q = 0) : d215057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213202, d215057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213300 q = 0) : d215125 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213300, d215125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213300, d215125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213301 q = 0) : d215126 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213301, d215126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213301, d215126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213302 q = 0) : d215127 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213302, d215127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213302, d215127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213327 q = 0) : d215149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213327, d215149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213327, d215149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20788 (p : Pattern) (selected : d213333 p = 0) : d215155 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213238 q = 0) : d215093 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213238, d215093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20763 q selected
    | true =>
      simp only [d213238, d215093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20764 q selected
  have h2 (q : Pattern) (selected : d213239 q = 0) : d215094 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213239, d215094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213239, d215094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213240 q = 0) : d215095 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213240, d215095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213240, d215095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213241 q = 0) : d215096 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213241, d215096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213241, d215096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213248 q = 0) : d215103 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213248, d215103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20765 q selected
    | true =>
      simp only [d213248, d215103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20766 q selected
  have h6 (q : Pattern) (selected : d213249 q = 0) : d215104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213249, d215104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213249, d215104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213250 q = 0) : d215105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213250, d215105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213250, d215105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213268 q = 0) : d215123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213268, d215123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20770 q selected
    | true =>
      simp only [d213268, d215123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20757 q selected
  have h9 (q : Pattern) (selected : d213298 q = 0) : d215070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213298, d215070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20776 q selected
    | true =>
      simp only [d213298, d215070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20777 q selected
  have h10 (q : Pattern) (selected : d213299 q = 0) : d215124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213299, d215124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213299, d215124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213304 q = 0) : d215129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213304, d215129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20778 q selected
    | true =>
      simp only [d213304, d215129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213305 q = 0) : d215130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213305, d215130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213305, d215130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213306 q = 0) : d215131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213306, d215131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213306, d215131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213307 q = 0) : d215132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213307, d215132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213307, d215132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213308 q = 0) : d215133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213308, d215133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213308, d215133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213312 q = 0) : d215137 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213312, d215137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20780 q selected
    | true =>
      simp only [d213312, d215137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20781 q selected
  have h17 (q : Pattern) (selected : d213313 q = 0) : d215138 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213313, d215138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213313, d215138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d213314 q = 0) : d215139 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213314, d215139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d213314, d215139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d213315 q = 0) : d215140 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213315, d215140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213315, d215140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d213318 q = 0) : d215143 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213318, d215143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20782 q selected
    | true =>
      simp only [d213318, d215143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20783 q selected
  have h21 (q : Pattern) (selected : d213319 q = 0) : d215144 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213319, d215144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213319, d215144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213320 q = 0) : d215145 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213320, d215145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d213320, d215145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d213322 q = 0) : d215147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213322, d215147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20784 q selected
    | true =>
      simp only [d213322, d215147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20760 q selected
  have h24 (q : Pattern) (selected : d213325 q = 0) : d215080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213325, d215080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20785 q selected
    | true =>
      simp only [d213325, d215080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20786 q selected
  have h25 (q : Pattern) (selected : d213326 q = 0) : d215148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213326, d215148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d213326, d215148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d213328 q = 0) : d215150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213328, d215150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20787 q selected
    | true =>
      simp only [d213328, d215150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d213329 q = 0) : d215151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213329, d215151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d213329, d215151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d213330 q = 0) : d215152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213330, d215152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d213330, d215152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d213331 q = 0) : d215153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213331, d215153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d213331, d215153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d213332 q = 0) : d215154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213332, d215154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d213332, d215154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d213333 q = 0) : d215155 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213333, d215155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d213333, d215155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro20789 (p : Pattern) (selected : d213340 p = 0) : d215162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213215 q = 0) : d215070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213215, d215070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20757 q selected
    | true =>
      simp only [d213215, d215070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20758 q selected
  have h2 (q : Pattern) (selected : d213216 q = 0) : d215071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213216, d215071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213216, d215071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213217 q = 0) : d215072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213217, d215072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213217, d215072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213218 q = 0) : d215073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213218, d215073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213218, d215073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213219 q = 0) : d215074 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213219, d215074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213219, d215074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213335 q = 0) : d215157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213335, d215157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20758 q selected
    | true =>
      simp only [d213335, d215157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213336 q = 0) : d215158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213336, d215158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213336, d215158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213337 q = 0) : d215159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213337, d215159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213337, d215159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213338 q = 0) : d215160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213338, d215160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213338, d215160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213339 q = 0) : d215161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213339, d215161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213339, d215161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213340 q = 0) : d215162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213340, d215162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213340, d215162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro20790 (p : Pattern) (selected : d213346 p = 0) : d215168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213335 q = 0) : d215157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213335, d215157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20758 q selected
    | true =>
      simp only [d213335, d215157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213336 q = 0) : d215158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213336, d215158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213336, d215158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213337 q = 0) : d215159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213337, d215159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213337, d215159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213338 q = 0) : d215160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213338, d215160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213338, d215160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213339 q = 0) : d215161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213339, d215161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213339, d215161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213341 q = 0) : d215163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213341, d215163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20761 q selected
    | true =>
      simp only [d213341, d215163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213342 q = 0) : d215164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213342, d215164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213342, d215164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213343 q = 0) : d215165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213343, d215165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213343, d215165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213344 q = 0) : d215166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213344, d215166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213344, d215166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213345 q = 0) : d215167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213345, d215167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213345, d215167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213346 q = 0) : d215168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213346, d215168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213346, d215168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro20791 (p : Pattern) (selected : d213353 p = 0) : d215175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213322 q = 0) : d215147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213322, d215147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20784 q selected
    | true =>
      simp only [d213322, d215147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20760 q selected
  have h2 (q : Pattern) (selected : d213325 q = 0) : d215080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213325, d215080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20785 q selected
    | true =>
      simp only [d213325, d215080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20786 q selected
  have h3 (q : Pattern) (selected : d213326 q = 0) : d215148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213326, d215148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213326, d215148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213328 q = 0) : d215150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213328, d215150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20787 q selected
    | true =>
      simp only [d213328, d215150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213329 q = 0) : d215151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213329, d215151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213329, d215151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213330 q = 0) : d215152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213330, d215152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213330, d215152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213351 q = 0) : d215173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213351, d215173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213351, d215173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213352 q = 0) : d215174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213352, d215174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213352, d215174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213353 q = 0) : d215175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213353, d215175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213353, d215175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20792 (p : Pattern) (selected : d213355 p = 0) : d215177 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213341 q = 0) : d215163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213341, d215163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20761 q selected
    | true =>
      simp only [d213341, d215163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213342 q = 0) : d215164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213342, d215164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213342, d215164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213343 q = 0) : d215165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213343, d215165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213343, d215165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213344 q = 0) : d215166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213344, d215166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213344, d215166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213345 q = 0) : d215167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213345, d215167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213345, d215167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213355 q = 0) : d215177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213355, d215177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213355, d215177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20793 (p : Pattern) (selected : d213363 p = 0) : d215185 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d965 q = 0) : d52584 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
  have h2 (q : Pattern) (selected : d834 q = 0) : d52511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d966 q = 0) : d52585 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d835 q = 0) : d52512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d967 q = 0) : d52586 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16356 q = 0) : d127213 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
  have h7 (q : Pattern) (selected : d9587 q = 0) : d101167 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
    | true =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16357 q = 0) : d127214 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d127214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16357, d127214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9589 q = 0) : d101169 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d16358 q = 0) : d127215 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16358, d127215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d16358, d127215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213361 q = 0) : d215183 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213361, d215183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213361, d215183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14644 q = 0) : d122847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
  have h13 (q : Pattern) (selected : d9597 q = 0) : d101177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14645 q = 0) : d122848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d122848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14645, d122848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9599 q = 0) : d101179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d14646 q = 0) : d122849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14646, d122849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d14646, d122849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d12858 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h18 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d12859 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d12860 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213362 q = 0) : d215184 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213362, d215184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213362, d215184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d213363 q = 0) : d215185 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213363, d215185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213363, d215185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20794 (p : Pattern) (selected : d213365 p = 0) : d215187 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d659 q = 0) : d52363 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
  have h2 (q : Pattern) (selected : d543 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d660 q = 0) : d52364 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d544 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d661 q = 0) : d52365 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16156 q = 0) : d127047 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
  have h7 (q : Pattern) (selected : d9458 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16157 q = 0) : d127048 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d127048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16157, d127048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9460 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d16158 q = 0) : d127049 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d127049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d16158, d127049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213097 q = 0) : d214975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213097, d214975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213097, d214975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d12858 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h13 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d12859 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d12860 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d971 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h18 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d972 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d973 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213364 q = 0) : d215186 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213364, d215186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213364, d215186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d213365 q = 0) : d215187 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213365, d215187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213365, d215187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20795 (p : Pattern) (selected : d213369 p = 0) : d215191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12858 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h2 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12859 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12860 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d971 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h7 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d972 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d973 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213364 q = 0) : d215186 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213364, d215186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213364, d215186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213368 q = 0) : d215190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213368, d215190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213368, d215190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213369 q = 0) : d215191 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213369, d215191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213369, d215191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20796 (p : Pattern) (selected : d213374 p = 0) : d215196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d412 q = 0) : d52178 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
  have h2 (q : Pattern) (selected : d319 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d413 q = 0) : d52179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d320 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d414 q = 0) : d52180 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d971 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h7 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d972 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d973 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213373 q = 0) : d215195 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213373, d215195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213373, d215195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213368 q = 0) : d215190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213368, d215190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213368, d215190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213374 q = 0) : d215196 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213374, d215196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213374, d215196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20797 (p : Pattern) (selected : d213377 p = 0) : d215199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d971 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h2 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d972 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d973 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213368 q = 0) : d215190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213368, d215190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213368, d215190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213377 q = 0) : d215199 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213377, d215199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213377, d215199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro20798 (p : Pattern) (selected : d213382 p = 0) : d215204 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213366 q = 0) : d215188 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213366, d215188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20793 q selected
    | true =>
      simp only [d213366, d215188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20794 q selected
  have h2 (q : Pattern) (selected : d213367 q = 0) : d215189 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213367, d215189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213367, d215189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213370 q = 0) : d215192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213370, d215192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20794 q selected
    | true =>
      simp only [d213370, d215192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20795 q selected
  have h4 (q : Pattern) (selected : d213371 q = 0) : d215193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213371, d215193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213371, d215193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213372 q = 0) : d215194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213372, d215194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213372, d215194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213375 q = 0) : d215197 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213375, d215197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20794 q selected
    | true =>
      simp only [d213375, d215197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20796 q selected
  have h7 (q : Pattern) (selected : d213376 q = 0) : d215198 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213376, d215198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213376, d215198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213378 q = 0) : d215200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213378, d215200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20796 q selected
    | true =>
      simp only [d213378, d215200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20797 q selected
  have h9 (q : Pattern) (selected : d213379 q = 0) : d215201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213379, d215201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213379, d215201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213380 q = 0) : d215202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213380, d215202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213380, d215202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213381 q = 0) : d215203 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213381, d215203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213381, d215203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213382 q = 0) : d215204 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213382, d215204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213382, d215204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro20799 (p : Pattern) (selected : d213387 p = 0) : d215209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213375 q = 0) : d215197 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213375, d215197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20794 q selected
    | true =>
      simp only [d213375, d215197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20796 q selected
  have h2 (q : Pattern) (selected : d213376 q = 0) : d215198 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213376, d215198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213376, d215198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213378 q = 0) : d215200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213378, d215200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20796 q selected
    | true =>
      simp only [d213378, d215200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20797 q selected
  have h4 (q : Pattern) (selected : d213379 q = 0) : d215201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213379, d215201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213379, d215201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213380 q = 0) : d215202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213380, d215202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213380, d215202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213385 q = 0) : d215207 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213385, d215207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213385, d215207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213386 q = 0) : d215208 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213386, d215208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213386, d215208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213387 q = 0) : d215209 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213387, d215209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213387, d215209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20800 (p : Pattern) (selected : d213393 p = 0) : d215215 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213383 q = 0) : d215205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213383, d215205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20798 q selected
    | true =>
      simp only [d213383, d215205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213384 q = 0) : d215206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213384, d215206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213384, d215206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213388 q = 0) : d215210 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213388, d215210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20799 q selected
    | true =>
      simp only [d213388, d215210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213389 q = 0) : d215211 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213389, d215211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213389, d215211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213390 q = 0) : d215212 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213390, d215212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213390, d215212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213391 q = 0) : d215213 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213391, d215213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213391, d215213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213392 q = 0) : d215214 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213392, d215214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213392, d215214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213393 q = 0) : d215215 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213393, d215215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213393, d215215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20801 (p : Pattern) (selected : d213395 p = 0) : d215217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213378 q = 0) : d215200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213378, d215200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20796 q selected
    | true =>
      simp only [d213378, d215200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20797 q selected
  have h2 (q : Pattern) (selected : d213379 q = 0) : d215201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213379, d215201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213379, d215201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213385 q = 0) : d215207 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213385, d215207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213385, d215207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213394 q = 0) : d215216 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213394, d215216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213394, d215216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213395 q = 0) : d215217 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213395, d215217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213395, d215217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20802 (p : Pattern) (selected : d213401 p = 0) : d215223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213388 q = 0) : d215210 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213388, d215210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20799 q selected
    | true =>
      simp only [d213388, d215210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213389 q = 0) : d215211 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213389, d215211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213389, d215211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213396 q = 0) : d215218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213396, d215218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20801 q selected
    | true =>
      simp only [d213396, d215218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213397 q = 0) : d215219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213397, d215219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213397, d215219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213398 q = 0) : d215220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213398, d215220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213398, d215220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213399 q = 0) : d215221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213399, d215221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213399, d215221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213400 q = 0) : d215222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213400, d215222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213400, d215222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213401 q = 0) : d215223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213401, d215223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213401, d215223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20803 (p : Pattern) (selected : d213405 p = 0) : d215187 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1013 q = 0) : d52363 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1013, d52363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1013, d52363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
  have h2 (q : Pattern) (selected : d868 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
    | true =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1014 q = 0) : d52364 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1014, d52364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1014, d52364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d869 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d869, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d869, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1015 q = 0) : d52365 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1015, d52365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1015, d52365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16393 q = 0) : d127047 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16393, d127047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16393, d127047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
  have h7 (q : Pattern) (selected : d9661 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
    | true =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16394 q = 0) : d127048 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16394, d127048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16394, d127048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9663 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9663, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9663, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d16395 q = 0) : d127049 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16395, d127049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d16395, d127049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213403 q = 0) : d214975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213403, d214975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213403, d214975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14689 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14689, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14689, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
  have h13 (q : Pattern) (selected : d9671 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
    | true =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14690 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14690, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14690, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9673 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d14691 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14691, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d14691, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d1018 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
  have h18 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d1019 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d1020 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213404 q = 0) : d215186 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213404, d215186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213404, d215186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d213405 q = 0) : d215187 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213405, d215187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213405, d215187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20804 (p : Pattern) (selected : d213408 p = 0) : d215196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d691 q = 0) : d52178 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d691, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d691, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
  have h2 (q : Pattern) (selected : d574 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d692 q = 0) : d52179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d692, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d692, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d575 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d693 q = 0) : d52180 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d693, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d693, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1018 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
  have h7 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1019 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1020 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213406 q = 0) : d215195 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213406, d215195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213406, d215195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213407 q = 0) : d215190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213407, d215190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213407, d215190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213408 q = 0) : d215196 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213408, d215196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213408, d215196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20805 (p : Pattern) (selected : d213411 p = 0) : d215199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1018 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
  have h2 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1019 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1020 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213407 q = 0) : d215190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213407, d215190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213407, d215190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213411 q = 0) : d215199 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213411, d215199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213411, d215199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro20806 (p : Pattern) (selected : d213417 p = 0) : d215209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213409 q = 0) : d215197 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213409, d215197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20803 q selected
    | true =>
      simp only [d213409, d215197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20804 q selected
  have h2 (q : Pattern) (selected : d213410 q = 0) : d215198 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213410, d215198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213410, d215198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213412 q = 0) : d215200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213412, d215200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20804 q selected
    | true =>
      simp only [d213412, d215200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20805 q selected
  have h4 (q : Pattern) (selected : d213413 q = 0) : d215201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213413, d215201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213413, d215201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213414 q = 0) : d215202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213414, d215202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213414, d215202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213415 q = 0) : d215207 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213415, d215207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213415, d215207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213416 q = 0) : d215208 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213416, d215208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213416, d215208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213417 q = 0) : d215209 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213417, d215209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213417, d215209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20807 (p : Pattern) (selected : d213421 p = 0) : d215217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213412 q = 0) : d215200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213412, d215200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20804 q selected
    | true =>
      simp only [d213412, d215200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20805 q selected
  have h2 (q : Pattern) (selected : d213413 q = 0) : d215201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213413, d215201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213413, d215201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213415 q = 0) : d215207 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213415, d215207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213415, d215207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213420 q = 0) : d215216 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213420, d215216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213420, d215216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213421 q = 0) : d215217 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213421, d215217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213421, d215217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20808 (p : Pattern) (selected : d213427 p = 0) : d215223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213418 q = 0) : d215210 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213418, d215210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20806 q selected
    | true =>
      simp only [d213418, d215210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213419 q = 0) : d215211 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213419, d215211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213419, d215211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213422 q = 0) : d215218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213422, d215218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20807 q selected
    | true =>
      simp only [d213422, d215218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213423 q = 0) : d215219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213423, d215219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213423, d215219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213424 q = 0) : d215220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213424, d215220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213424, d215220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213425 q = 0) : d215221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213425, d215221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213425, d215221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213426 q = 0) : d215222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213426, d215222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213426, d215222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213427 q = 0) : d215223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213427, d215223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213427, d215223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20809 (p : Pattern) (selected : d213431 p = 0) : d215228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213422 q = 0) : d215218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213422, d215218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20807 q selected
    | true =>
      simp only [d213422, d215218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213423 q = 0) : d215219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213423, d215219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213423, d215219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213428 q = 0) : d215225 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213428, d215225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213428, d215225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213429 q = 0) : d215226 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213429, d215226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213429, d215226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213430 q = 0) : d215227 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213430, d215227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213430, d215227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213431 q = 0) : d215228 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213431, d215228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213431, d215228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20810 (p : Pattern) (selected : d213437 p = 0) : d215234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213388 q = 0) : d215210 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213388, d215210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20799 q selected
    | true =>
      simp only [d213388, d215210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213389 q = 0) : d215211 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213389, d215211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213389, d215211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213434 q = 0) : d215231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213434, d215231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213434, d215231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213435 q = 0) : d215232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213435, d215232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213435, d215232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213436 q = 0) : d215233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213436, d215233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213436, d215233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213437 q = 0) : d215234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213437, d215234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213437, d215234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20811 (p : Pattern) (selected : d213443 p = 0) : d215240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213402 q = 0) : d215224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213402, d215224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20800 q selected
    | true =>
      simp only [d213402, d215224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20802 q selected
  have h2 (q : Pattern) (selected : d213432 q = 0) : d215229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213432, d215229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20808 q selected
    | true =>
      simp only [d213432, d215229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20809 q selected
  have h3 (q : Pattern) (selected : d213433 q = 0) : d215230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213433, d215230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213433, d215230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213438 q = 0) : d215235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213438, d215235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20810 q selected
    | true =>
      simp only [d213438, d215235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213439 q = 0) : d215236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213439, d215236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213439, d215236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213440 q = 0) : d215237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213440, d215237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213440, d215237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213441 q = 0) : d215238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213441, d215238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213441, d215238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213442 q = 0) : d215239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213442, d215239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213442, d215239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213443 q = 0) : d215240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213443, d215240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213443, d215240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20812 (p : Pattern) (selected : d213448 p = 0) : d215228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213396 q = 0) : d215218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213396, d215218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20801 q selected
    | true =>
      simp only [d213396, d215218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213397 q = 0) : d215219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213397, d215219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213397, d215219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213445 q = 0) : d215225 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213445, d215225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213445, d215225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213446 q = 0) : d215226 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213446, d215226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213446, d215226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213447 q = 0) : d215227 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213447, d215227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213447, d215227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213448 q = 0) : d215228 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213448, d215228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213448, d215228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20813 (p : Pattern) (selected : d213454 p = 0) : d215247 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213449 q = 0) : d215242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213449, d215242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20812 q selected
    | true =>
      simp only [d213449, d215242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213450 q = 0) : d215243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213450, d215243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213450, d215243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213451 q = 0) : d215244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213451, d215244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213451, d215244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213452 q = 0) : d215245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213452, d215245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213452, d215245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213453 q = 0) : d215246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213453, d215246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213453, d215246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213454 q = 0) : d215247 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213454, d215247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213454, d215247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20814 (p : Pattern) (selected : d213460 p = 0) : d215253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213221 q = 0) : d215076 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213221, d215076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213221, d215076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20759 q selected
  have h2 (q : Pattern) (selected : d213222 q = 0) : d215077 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213222, d215077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213222, d215077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d213231 q = 0) : d215086 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213231, d215086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20759 q selected
    | true =>
      simp only [d213231, d215086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20762 q selected
  have h4 (q : Pattern) (selected : d213232 q = 0) : d215087 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213232, d215087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213232, d215087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213233 q = 0) : d215088 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213233, d215088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213233, d215088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213334 q = 0) : d215156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213334, d215156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20779 q selected
    | true =>
      simp only [d213334, d215156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20788 q selected
  have h7 (q : Pattern) (selected : d213347 q = 0) : d215169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213347, d215169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20789 q selected
    | true =>
      simp only [d213347, d215169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20790 q selected
  have h8 (q : Pattern) (selected : d213348 q = 0) : d215170 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213348, d215170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213348, d215170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213349 q = 0) : d215171 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213349, d215171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213349, d215171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d213350 q = 0) : d215172 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213350, d215172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213350, d215172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213354 q = 0) : d215176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213354, d215176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213354, d215176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20791 q selected
  have h12 (q : Pattern) (selected : d213356 q = 0) : d215178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213356, d215178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213356, d215178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20792 q selected
  have h13 (q : Pattern) (selected : d213357 q = 0) : d215179 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213357, d215179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213357, d215179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213358 q = 0) : d215180 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213358, d215180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d213358, d215180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d213359 q = 0) : d215181 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213359, d215181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d213359, d215181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d213360 q = 0) : d215182 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213360, d215182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213360, d215182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d213444 q = 0) : d215241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213444, d215241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213444, d215241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20811 q selected
  have h18 (q : Pattern) (selected : d213455 q = 0) : d215248 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213455, d215248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213455, d215248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20813 q selected
  have h19 (q : Pattern) (selected : d213456 q = 0) : d215249 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213456, d215249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d213456, d215249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d213457 q = 0) : d215250 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213457, d215250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d213457, d215250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d213458 q = 0) : d215251 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213458, d215251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d213458, d215251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d213459 q = 0) : d215252 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213459, d215252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d213459, d215252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d213460 q = 0) : d215253 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d213460, d215253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213460, d215253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20815 (p : Pattern) (selected : d213466 p = 0) : d215259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213461 q = 0) : d215254 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d213461, d215254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213461, d215254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20814 q selected
  have h2 (q : Pattern) (selected : d213462 q = 0) : d215255 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d213462, d215255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213462, d215255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213463 q = 0) : d215256 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d213463, d215256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213463, d215256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213464 q = 0) : d215257 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d213464, d215257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213464, d215257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213465 q = 0) : d215258 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d213465, d215258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213465, d215258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213466 q = 0) : d215259 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d213466, d215259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213466, d215259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20816 (p : Pattern) (selected : d213471 p = 0) : d215264 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1100 q = 0) : d52681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro386 q selected
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1101 q = 0) : d52682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1102 q = 0) : d52683 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9789 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
    | true =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9791 q = 0) : d101312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16438 q = 0) : d127276 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16438, d127276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16438, d127276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213469 q = 0) : d215262 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213469, d215262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213469, d215262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9780 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14758 q = 0) : d122929 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14763 q = 0) : d122934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213470 q = 0) : d215263 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213470, d215263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213470, d215263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213471 q = 0) : d215264 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213471, d215264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213471, d215264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20817 (p : Pattern) (selected : d213474 p = 0) : d215267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1110 q = 0) : d52691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro387 q selected
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1111 q = 0) : d52692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1112 q = 0) : d52693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1123 q = 0) : d52704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213472 q = 0) : d215265 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213472, d215265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213472, d215265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14763 q = 0) : d122934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213473 q = 0) : d215266 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213473, d215266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213473, d215266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213474 q = 0) : d215267 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213474, d215267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213474, d215267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro20818 (p : Pattern) (selected : d213479 p = 0) : d215272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5018 q = 0) : d69108 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2799 q selected
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5019 q = 0) : d69109 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5020 q = 0) : d69110 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, d69110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5020, d69110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213477 q = 0) : d215270 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213477, d215270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213477, d215270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9846 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14770 q = 0) : d122941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213478 q = 0) : d215271 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213478, d215271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213478, d215271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213479 q = 0) : d215272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213479, d215272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213479, d215272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20819 (p : Pattern) (selected : d213484 p = 0) : d215277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1123 q = 0) : d52704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213483 q = 0) : d215276 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213483, d215276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213483, d215276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9846 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14770 q = 0) : d122941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213478 q = 0) : d215271 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213478, d215271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213478, d215271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213484 q = 0) : d215277 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213484, d215277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213484, d215277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20820 (p : Pattern) (selected : d213489 p = 0) : d215282 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213475 q = 0) : d215268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213475, d215268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20816 q selected
    | true =>
      simp only [d213475, d215268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
  have h2 (q : Pattern) (selected : d213476 q = 0) : d215269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213476, d215269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213476, d215269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213480 q = 0) : d215273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213480, d215273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
    | true =>
      simp only [d213480, d215273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20818 q selected
  have h4 (q : Pattern) (selected : d213481 q = 0) : d215274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213481, d215274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213481, d215274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213482 q = 0) : d215275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213482, d215275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213482, d215275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213485 q = 0) : d215278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213485, d215278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
    | true =>
      simp only [d213485, d215278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20819 q selected
  have h7 (q : Pattern) (selected : d213486 q = 0) : d215279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213486, d215279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213486, d215279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213487 q = 0) : d215280 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213487, d215280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213487, d215280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213488 q = 0) : d215281 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213488, d215281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213488, d215281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213489 q = 0) : d215282 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213489, d215282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213489, d215282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20821 (p : Pattern) (selected : d213493 p = 0) : d215286 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213485 q = 0) : d215278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213485, d215278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
    | true =>
      simp only [d213485, d215278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20819 q selected
  have h2 (q : Pattern) (selected : d213486 q = 0) : d215279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213486, d215279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213486, d215279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213487 q = 0) : d215280 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213487, d215280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213487, d215280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213492 q = 0) : d215285 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213492, d215285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213492, d215285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213493 q = 0) : d215286 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213493, d215286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213493, d215286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20822 (p : Pattern) (selected : d213499 p = 0) : d215292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213490 q = 0) : d215283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20820 q selected
    | true =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213491 q = 0) : d215284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213496 q = 0) : d215289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213497 q = 0) : d215290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213497, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213497, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213498 q = 0) : d215291 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213498, d215291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213498, d215291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213499 q = 0) : d215292 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213499, d215292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213499, d215292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20823 (p : Pattern) (selected : d213503 p = 0) : d215296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213500 q = 0) : d215293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213501 q = 0) : d215294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213501, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213501, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213502 q = 0) : d215295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213502, d215295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213502, d215295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213503 q = 0) : d215296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213503, d215296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213503, d215296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20824 (p : Pattern) (selected : d213509 p = 0) : d215302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213504 q = 0) : d215297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213504, d215297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20822 q selected
    | true =>
      simp only [d213504, d215297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20823 q selected
  have h2 (q : Pattern) (selected : d213505 q = 0) : d215298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213505, d215298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213505, d215298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213506 q = 0) : d215299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213506, d215299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213506, d215299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213507 q = 0) : d215300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213507, d215300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213507, d215300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213508 q = 0) : d215301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213508, d215301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213508, d215301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213509 q = 0) : d215302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213509, d215302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213509, d215302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20825 (p : Pattern) (selected : d213512 p = 0) : d215305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213490 q = 0) : d215283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20820 q selected
    | true =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213491 q = 0) : d215284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213496 q = 0) : d215289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213497 q = 0) : d215290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213497, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213497, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213498 q = 0) : d215291 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213498, d215291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213498, d215291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213512 q = 0) : d215305 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213512, d215305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213512, d215305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20826 (p : Pattern) (selected : d213513 p = 0) : d215306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213500 q = 0) : d215293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213501 q = 0) : d215294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213501, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213501, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213502 q = 0) : d215295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213502, d215295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213502, d215295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213513 q = 0) : d215306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213513, d215306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213513, d215306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20827 (p : Pattern) (selected : d213519 p = 0) : d215312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213504 q = 0) : d215297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213504, d215297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20822 q selected
    | true =>
      simp only [d213504, d215297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20823 q selected
  have h2 (q : Pattern) (selected : d213505 q = 0) : d215298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213505, d215298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213505, d215298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213506 q = 0) : d215299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213506, d215299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213506, d215299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213507 q = 0) : d215300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213507, d215300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213507, d215300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213508 q = 0) : d215301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213508, d215301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213508, d215301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213514 q = 0) : d215307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213514, d215307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20825 q selected
    | true =>
      simp only [d213514, d215307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20826 q selected
  have h7 (q : Pattern) (selected : d213515 q = 0) : d215308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213515, d215308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213515, d215308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213516 q = 0) : d215309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213516, d215309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213516, d215309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213517 q = 0) : d215310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213517, d215310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213517, d215310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213518 q = 0) : d215311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213518, d215311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213518, d215311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213519 q = 0) : d215312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213519, d215312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213519, d215312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro20828 (p : Pattern) (selected : d213524 p = 0) : d215317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213490 q = 0) : d215283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20820 q selected
    | true =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213491 q = 0) : d215284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213496 q = 0) : d215289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213497 q = 0) : d215290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213497, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213497, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213523 q = 0) : d215316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213523, d215316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213523, d215316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213524 q = 0) : d215317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213524, d215317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213524, d215317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20829 (p : Pattern) (selected : d213526 p = 0) : d215319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213500 q = 0) : d215293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213501 q = 0) : d215294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213501, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213501, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213525 q = 0) : d215318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213525, d215318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213525, d215318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213526 q = 0) : d215319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213526, d215319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213526, d215319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20830 (p : Pattern) (selected : d213533 p = 0) : d215326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213490 q = 0) : d215283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20820 q selected
    | true =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213491 q = 0) : d215284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213496 q = 0) : d215289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213531 q = 0) : d215324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213531, d215324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213531, d215324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213532 q = 0) : d215325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213532, d215325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213532, d215325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213533 q = 0) : d215326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213533, d215326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213533, d215326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20831 (p : Pattern) (selected : d213536 p = 0) : d215329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213500 q = 0) : d215293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213534 q = 0) : d215327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213534, d215327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213534, d215327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213535 q = 0) : d215328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213535, d215328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213535, d215328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213536 q = 0) : d215329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213536, d215329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213536, d215329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20832 (p : Pattern) (selected : d213542 p = 0) : d215335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1210 q = 0) : d52791 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro407 q selected
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1211 q = 0) : d52792 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1212 q = 0) : d52793 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9753 q = 0) : d101274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
    | true =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9755 q = 0) : d101276 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16507 q = 0) : d127345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16507, d127345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16507, d127345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213540 q = 0) : d215333 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213540, d215333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213540, d215333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9763 q = 0) : d101284 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
    | true =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9765 q = 0) : d101286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14836 q = 0) : d123007 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14836, d123007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14836, d123007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9780 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14758 q = 0) : d122929 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213541 q = 0) : d215334 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213541, d215334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213541, d215334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213542 q = 0) : d215335 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213542, d215335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213542, d215335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20833 (p : Pattern) (selected : d213546 p = 0) : d215339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9814 q = 0) : d101335 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6677 q selected
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9816 q = 0) : d101337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13022 q = 0) : d113352 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, d113352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13022, d113352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14763 q = 0) : d122934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213545 q = 0) : d215338 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213545, d215338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213545, d215338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213473 q = 0) : d215266 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213473, d215266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213473, d215266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213546 q = 0) : d215339 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213546, d215339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213546, d215339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20834 (p : Pattern) (selected : d213551 p = 0) : d215344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213543 q = 0) : d215336 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213543, d215336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20832 q selected
    | true =>
      simp only [d213543, d215336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20816 q selected
  have h2 (q : Pattern) (selected : d213544 q = 0) : d215337 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213544, d215337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213544, d215337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213547 q = 0) : d215340 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213547, d215340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20816 q selected
    | true =>
      simp only [d213547, d215340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20833 q selected
  have h4 (q : Pattern) (selected : d213548 q = 0) : d215341 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213548, d215341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213548, d215341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213549 q = 0) : d215342 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213549, d215342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213549, d215342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213475 q = 0) : d215268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213475, d215268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20816 q selected
    | true =>
      simp only [d213475, d215268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
  have h7 (q : Pattern) (selected : d213476 q = 0) : d215269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213476, d215269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213476, d215269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213480 q = 0) : d215273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213480, d215273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
    | true =>
      simp only [d213480, d215273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20818 q selected
  have h9 (q : Pattern) (selected : d213481 q = 0) : d215274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213481, d215274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213481, d215274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213482 q = 0) : d215275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213482, d215275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213482, d215275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213550 q = 0) : d215343 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213550, d215343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213550, d215343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213551 q = 0) : d215344 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213551, d215344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213551, d215344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro20835 (p : Pattern) (selected : d213556 p = 0) : d215349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213475 q = 0) : d215268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213475, d215268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20816 q selected
    | true =>
      simp only [d213475, d215268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
  have h2 (q : Pattern) (selected : d213476 q = 0) : d215269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213476, d215269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213476, d215269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213480 q = 0) : d215273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213480, d215273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
    | true =>
      simp only [d213480, d215273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20818 q selected
  have h4 (q : Pattern) (selected : d213481 q = 0) : d215274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213481, d215274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213481, d215274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213482 q = 0) : d215275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213482, d215275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213482, d215275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213554 q = 0) : d215347 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213554, d215347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213554, d215347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213555 q = 0) : d215348 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213555, d215348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213555, d215348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213556 q = 0) : d215349 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213556, d215349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213556, d215349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20836 (p : Pattern) (selected : d213562 p = 0) : d215355 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213552 q = 0) : d215345 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213552, d215345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20834 q selected
    | true =>
      simp only [d213552, d215345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213553 q = 0) : d215346 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213553, d215346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213553, d215346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213557 q = 0) : d215350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213557, d215350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20835 q selected
    | true =>
      simp only [d213557, d215350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213558 q = 0) : d215351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213558, d215351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213558, d215351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213559 q = 0) : d215352 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213559, d215352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213559, d215352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213560 q = 0) : d215353 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213560, d215353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213560, d215353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213561 q = 0) : d215354 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213561, d215354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213561, d215354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213562 q = 0) : d215355 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213562, d215355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213562, d215355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20837 (p : Pattern) (selected : d213566 p = 0) : d215359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213557 q = 0) : d215350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213557, d215350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20835 q selected
    | true =>
      simp only [d213557, d215350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213558 q = 0) : d215351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213558, d215351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213558, d215351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213563 q = 0) : d215356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213563, d215356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213563, d215356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213564 q = 0) : d215357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213564, d215357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213564, d215357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213565 q = 0) : d215358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213565, d215358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213565, d215358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213566 q = 0) : d215359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213566, d215359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213566, d215359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20838 (p : Pattern) (selected : d213570 p = 0) : d215264 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1255 q = 0) : d52681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1255, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro415 q selected
    | true =>
      simp only [d1255, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1256 q = 0) : d52682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1256, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1256, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1257 q = 0) : d52683 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1257, d52683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1257, d52683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9896 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
    | true =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9898 q = 0) : d101312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9898, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9898, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16539 q = 0) : d127276 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16539, d127276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16539, d127276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213568 q = 0) : d215262 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213568, d215262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213568, d215262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9908 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
    | true =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9910 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9910, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9910, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14868 q = 0) : d122929 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14868, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14868, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9920 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14873 q = 0) : d122934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14873, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14873, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213569 q = 0) : d215263 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213569, d215263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213569, d215263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213570 q = 0) : d215264 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213570, d215264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213570, d215264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20839 (p : Pattern) (selected : d213573 p = 0) : d215267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1265 q = 0) : d52691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro416 q selected
    | true =>
      simp only [d1265, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1266 q = 0) : d52692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1266, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1267 q = 0) : d52693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1267, d52693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1267, d52693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1277 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1278 q = 0) : d52704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213571 q = 0) : d215265 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213571, d215265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213571, d215265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9920 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14873 q = 0) : d122934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14873, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14873, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213572 q = 0) : d215266 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213572, d215266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213572, d215266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213573 q = 0) : d215267 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213573, d215267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213573, d215267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro20840 (p : Pattern) (selected : d213578 p = 0) : d215272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9943 q = 0) : d69108 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6695 q selected
    | true =>
      simp only [d9943, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9945 q = 0) : d69109 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9945, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9945, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13057 q = 0) : d69110 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13057, d69110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13057, d69110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213576 q = 0) : d215270 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213576, d215270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213576, d215270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9954 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14880 q = 0) : d122941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14880, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14880, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213577 q = 0) : d215271 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213577, d215271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213577, d215271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213578 q = 0) : d215272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213578, d215272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213578, d215272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20841 (p : Pattern) (selected : d213583 p = 0) : d215277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1277 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1278 q = 0) : d52704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213582 q = 0) : d215276 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213582, d215276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213582, d215276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9954 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14880 q = 0) : d122941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14880, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14880, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213577 q = 0) : d215271 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213577, d215271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213577, d215271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213583 q = 0) : d215277 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213583, d215277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213583, d215277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20842 (p : Pattern) (selected : d213588 p = 0) : d215282 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213574 q = 0) : d215268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213574, d215268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20838 q selected
    | true =>
      simp only [d213574, d215268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20839 q selected
  have h2 (q : Pattern) (selected : d213575 q = 0) : d215269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213575, d215269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213575, d215269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213579 q = 0) : d215273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213579, d215273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20839 q selected
    | true =>
      simp only [d213579, d215273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20840 q selected
  have h4 (q : Pattern) (selected : d213580 q = 0) : d215274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213580, d215274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213580, d215274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213581 q = 0) : d215275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213581, d215275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213581, d215275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213584 q = 0) : d215278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213584, d215278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20839 q selected
    | true =>
      simp only [d213584, d215278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20841 q selected
  have h7 (q : Pattern) (selected : d213585 q = 0) : d215279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213585, d215279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213585, d215279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213586 q = 0) : d215280 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213586, d215280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213586, d215280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213587 q = 0) : d215281 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213587, d215281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213587, d215281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213588 q = 0) : d215282 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213588, d215282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213588, d215282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20843 (p : Pattern) (selected : d213592 p = 0) : d215286 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213584 q = 0) : d215278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213584, d215278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20839 q selected
    | true =>
      simp only [d213584, d215278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20841 q selected
  have h2 (q : Pattern) (selected : d213585 q = 0) : d215279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213585, d215279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213585, d215279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213586 q = 0) : d215280 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213586, d215280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213586, d215280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213591 q = 0) : d215285 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213591, d215285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213591, d215285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213592 q = 0) : d215286 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213592, d215286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213592, d215286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20844 (p : Pattern) (selected : d213598 p = 0) : d215292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213589 q = 0) : d215283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213589, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20842 q selected
    | true =>
      simp only [d213589, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213590 q = 0) : d215284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213590, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213590, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213593 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213593, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20843 q selected
    | true =>
      simp only [d213593, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213594 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213594, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213594, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213595 q = 0) : d215289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213595, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213595, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213596 q = 0) : d215290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213596, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213596, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213597 q = 0) : d215291 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213597, d215291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213597, d215291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213598 q = 0) : d215292 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213598, d215292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213598, d215292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20845 (p : Pattern) (selected : d213602 p = 0) : d215296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213593 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213593, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20843 q selected
    | true =>
      simp only [d213593, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213594 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213594, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213594, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213599 q = 0) : d215293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213599, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213599, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213600 q = 0) : d215294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213600, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213600, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213601 q = 0) : d215295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213601, d215295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213601, d215295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213602 q = 0) : d215296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213602, d215296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213602, d215296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20846 (p : Pattern) (selected : d213605 p = 0) : d215362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1123 q = 0) : d52704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213483 q = 0) : d215276 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213483, d215276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213483, d215276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213605 q = 0) : d215362 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213605, d215362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213605, d215362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20847 (p : Pattern) (selected : d213610 p = 0) : d215367 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213475 q = 0) : d215268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213475, d215268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20816 q selected
    | true =>
      simp only [d213475, d215268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
  have h2 (q : Pattern) (selected : d213476 q = 0) : d215269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213476, d215269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213476, d215269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213480 q = 0) : d215273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213480, d215273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
    | true =>
      simp only [d213480, d215273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20818 q selected
  have h4 (q : Pattern) (selected : d213481 q = 0) : d215274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213481, d215274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213481, d215274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213482 q = 0) : d215275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213482, d215275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213482, d215275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213606 q = 0) : d215363 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213606, d215363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20817 q selected
    | true =>
      simp only [d213606, d215363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20846 q selected
  have h7 (q : Pattern) (selected : d213607 q = 0) : d215364 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213607, d215364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213607, d215364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213608 q = 0) : d215365 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213608, d215365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213608, d215365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213609 q = 0) : d215366 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213609, d215366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213609, d215366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213610 q = 0) : d215367 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213610, d215367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213610, d215367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20848 (p : Pattern) (selected : d213616 p = 0) : d215373 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213611 q = 0) : d215368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213611, d215368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20847 q selected
    | true =>
      simp only [d213611, d215368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213612 q = 0) : d215369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213612, d215369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213612, d215369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213613 q = 0) : d215370 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213613, d215370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213613, d215370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213614 q = 0) : d215371 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213614, d215371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213614, d215371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213615 q = 0) : d215372 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213615, d215372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213615, d215372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213616 q = 0) : d215373 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213616, d215373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213616, d215373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20849 (p : Pattern) (selected : d213622 p = 0) : d215379 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213527 q = 0) : d215320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213527, d215320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20828 q selected
    | true =>
      simp only [d213527, d215320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20829 q selected
  have h2 (q : Pattern) (selected : d213528 q = 0) : d215321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213528, d215321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213528, d215321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213529 q = 0) : d215322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213529, d215322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213529, d215322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213530 q = 0) : d215323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213530, d215323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213530, d215323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213537 q = 0) : d215330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213537, d215330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20830 q selected
    | true =>
      simp only [d213537, d215330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20831 q selected
  have h6 (q : Pattern) (selected : d213538 q = 0) : d215331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213538, d215331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213538, d215331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213539 q = 0) : d215332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213539, d215332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213539, d215332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213567 q = 0) : d215360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213567, d215360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20836 q selected
    | true =>
      simp only [d213567, d215360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20837 q selected
  have h9 (q : Pattern) (selected : d213603 q = 0) : d215297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213603, d215297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20844 q selected
    | true =>
      simp only [d213603, d215297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20845 q selected
  have h10 (q : Pattern) (selected : d213604 q = 0) : d215361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213604, d215361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213604, d215361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213617 q = 0) : d215374 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213617, d215374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20848 q selected
    | true =>
      simp only [d213617, d215374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213618 q = 0) : d215375 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213618, d215375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213618, d215375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213619 q = 0) : d215376 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213619, d215376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213619, d215376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213620 q = 0) : d215377 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213620, d215377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213620, d215377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213621 q = 0) : d215378 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213621, d215378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213621, d215378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213622 q = 0) : d215379 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213622, d215379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213622, d215379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro20850 (p : Pattern) (selected : d213623 p = 0) : d215380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213490 q = 0) : d215283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20820 q selected
    | true =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213491 q = 0) : d215284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213496 q = 0) : d215289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213497 q = 0) : d215290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213497, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213497, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213523 q = 0) : d215316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213523, d215316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213523, d215316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213623 q = 0) : d215380 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213623, d215380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213623, d215380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20851 (p : Pattern) (selected : d213624 p = 0) : d215381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213500 q = 0) : d215293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213501 q = 0) : d215294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213501, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213501, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213525 q = 0) : d215318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213525, d215318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213525, d215318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213624 q = 0) : d215381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213624, d215381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213624, d215381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20852 (p : Pattern) (selected : d213629 p = 0) : d215386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213490 q = 0) : d215283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20820 q selected
    | true =>
      simp only [d213490, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213491 q = 0) : d215284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213491, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213496 q = 0) : d215289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213496, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213531 q = 0) : d215324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213531, d215324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213531, d215324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213532 q = 0) : d215325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213532, d215325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213532, d215325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213629 q = 0) : d215386 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213629, d215386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213629, d215386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20853 (p : Pattern) (selected : d213630 p = 0) : d215387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213500 q = 0) : d215293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213500, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213534 q = 0) : d215327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213534, d215327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213534, d215327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213535 q = 0) : d215328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213535, d215328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213535, d215328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213630 q = 0) : d215387 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213630, d215387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213630, d215387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20854 (p : Pattern) (selected : d213634 p = 0) : d215391 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213552 q = 0) : d215345 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213552, d215345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20834 q selected
    | true =>
      simp only [d213552, d215345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213553 q = 0) : d215346 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213553, d215346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213553, d215346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213557 q = 0) : d215350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213557, d215350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20835 q selected
    | true =>
      simp only [d213557, d215350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213558 q = 0) : d215351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213558, d215351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213558, d215351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213559 q = 0) : d215352 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213559, d215352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213559, d215352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213560 q = 0) : d215353 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213560, d215353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213560, d215353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213561 q = 0) : d215354 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213561, d215354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213561, d215354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213634 q = 0) : d215391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213634, d215391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213634, d215391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20855 (p : Pattern) (selected : d213635 p = 0) : d215392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213557 q = 0) : d215350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213557, d215350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20835 q selected
    | true =>
      simp only [d213557, d215350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213558 q = 0) : d215351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213558, d215351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213558, d215351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213494 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20821 q selected
    | true =>
      simp only [d213494, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213495 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213495, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213563 q = 0) : d215356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213563, d215356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213563, d215356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213564 q = 0) : d215357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213564, d215357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213564, d215357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213565 q = 0) : d215358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213565, d215358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213565, d215358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213635 q = 0) : d215392 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213635, d215392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213635, d215392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20856 (p : Pattern) (selected : d213637 p = 0) : d215305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213589 q = 0) : d215283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213589, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20842 q selected
    | true =>
      simp only [d213589, d215283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213590 q = 0) : d215284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213590, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213590, d215284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213593 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213593, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20843 q selected
    | true =>
      simp only [d213593, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213594 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213594, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213594, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213595 q = 0) : d215289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213595, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213595, d215289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213596 q = 0) : d215290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213596, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213596, d215290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213597 q = 0) : d215291 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213597, d215291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213597, d215291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213637 q = 0) : d215305 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213637, d215305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213637, d215305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20857 (p : Pattern) (selected : d213638 p = 0) : d215306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213593 q = 0) : d215287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213593, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20843 q selected
    | true =>
      simp only [d213593, d215287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213594 q = 0) : d215288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213594, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213594, d215288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213599 q = 0) : d215293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213599, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213599, d215293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213600 q = 0) : d215294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213600, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213600, d215294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213601 q = 0) : d215295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213601, d215295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213601, d215295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213638 q = 0) : d215306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213638, d215306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213638, d215306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20858 (p : Pattern) (selected : d213641 p = 0) : d215395 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213611 q = 0) : d215368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213611, d215368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20847 q selected
    | true =>
      simp only [d213611, d215368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213612 q = 0) : d215369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213612, d215369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213612, d215369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213613 q = 0) : d215370 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213613, d215370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213613, d215370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213614 q = 0) : d215371 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213614, d215371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213614, d215371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213615 q = 0) : d215372 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213615, d215372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213615, d215372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213641 q = 0) : d215395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213641, d215395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213641, d215395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20859 (p : Pattern) (selected : d213647 p = 0) : d215401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213527 q = 0) : d215320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213527, d215320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20828 q selected
    | true =>
      simp only [d213527, d215320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20829 q selected
  have h2 (q : Pattern) (selected : d213528 q = 0) : d215321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213528, d215321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213528, d215321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213529 q = 0) : d215322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213529, d215322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213529, d215322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213530 q = 0) : d215323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213530, d215323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213530, d215323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213537 q = 0) : d215330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213537, d215330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20830 q selected
    | true =>
      simp only [d213537, d215330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20831 q selected
  have h6 (q : Pattern) (selected : d213538 q = 0) : d215331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213538, d215331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213538, d215331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213539 q = 0) : d215332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213539, d215332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213539, d215332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213567 q = 0) : d215360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213567, d215360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20836 q selected
    | true =>
      simp only [d213567, d215360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20837 q selected
  have h9 (q : Pattern) (selected : d213603 q = 0) : d215297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213603, d215297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20844 q selected
    | true =>
      simp only [d213603, d215297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20845 q selected
  have h10 (q : Pattern) (selected : d213604 q = 0) : d215361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213604, d215361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213604, d215361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213617 q = 0) : d215374 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213617, d215374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20848 q selected
    | true =>
      simp only [d213617, d215374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213618 q = 0) : d215375 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213618, d215375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213618, d215375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213619 q = 0) : d215376 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213619, d215376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213619, d215376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213620 q = 0) : d215377 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213620, d215377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213620, d215377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213621 q = 0) : d215378 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213621, d215378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213621, d215378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213625 q = 0) : d215382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213625, d215382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20850 q selected
    | true =>
      simp only [d213625, d215382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20851 q selected
  have h17 (q : Pattern) (selected : d213626 q = 0) : d215383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213626, d215383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213626, d215383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d213627 q = 0) : d215384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213627, d215384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d213627, d215384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d213628 q = 0) : d215385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213628, d215385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213628, d215385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d213631 q = 0) : d215388 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213631, d215388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20852 q selected
    | true =>
      simp only [d213631, d215388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20853 q selected
  have h21 (q : Pattern) (selected : d213632 q = 0) : d215389 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213632, d215389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213632, d215389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213633 q = 0) : d215390 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213633, d215390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d213633, d215390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d213636 q = 0) : d215393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213636, d215393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20854 q selected
    | true =>
      simp only [d213636, d215393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20855 q selected
  have h24 (q : Pattern) (selected : d213639 q = 0) : d215307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213639, d215307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20856 q selected
    | true =>
      simp only [d213639, d215307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20857 q selected
  have h25 (q : Pattern) (selected : d213640 q = 0) : d215394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213640, d215394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d213640, d215394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d213642 q = 0) : d215396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213642, d215396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20858 q selected
    | true =>
      simp only [d213642, d215396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d213643 q = 0) : d215397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213643, d215397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d213643, d215397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d213644 q = 0) : d215398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213644, d215398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d213644, d215398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d213645 q = 0) : d215399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213645, d215399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d213645, d215399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d213646 q = 0) : d215400 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213646, d215400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d213646, d215400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d213647 q = 0) : d215401 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213647, d215401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d213647, d215401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro20860 (p : Pattern) (selected : d213659 p = 0) : d215413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213649 q = 0) : d215403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213649, d215403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20837 q selected
    | true =>
      simp only [d213649, d215403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20823 q selected
  have h2 (q : Pattern) (selected : d213650 q = 0) : d215404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213650, d215404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213650, d215404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213651 q = 0) : d215405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213651, d215405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213651, d215405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213652 q = 0) : d215406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213652, d215406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213652, d215406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213653 q = 0) : d215407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213653, d215407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213653, d215407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213654 q = 0) : d215408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213654, d215408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20823 q selected
    | true =>
      simp only [d213654, d215408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213655 q = 0) : d215409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213655, d215409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213655, d215409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213656 q = 0) : d215410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213656, d215410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213656, d215410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213657 q = 0) : d215411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213657, d215411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213657, d215411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213658 q = 0) : d215412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213658, d215412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213658, d215412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213659 q = 0) : d215413 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213659, d215413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213659, d215413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro20861 (p : Pattern) (selected : d213665 p = 0) : d215419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213654 q = 0) : d215408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213654, d215408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20823 q selected
    | true =>
      simp only [d213654, d215408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213655 q = 0) : d215409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213655, d215409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213655, d215409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213656 q = 0) : d215410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213656, d215410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213656, d215410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213657 q = 0) : d215411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213657, d215411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213657, d215411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213658 q = 0) : d215412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213658, d215412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213658, d215412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213660 q = 0) : d215414 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213660, d215414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20826 q selected
    | true =>
      simp only [d213660, d215414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213661 q = 0) : d215415 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213661, d215415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213661, d215415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213662 q = 0) : d215416 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213662, d215416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213662, d215416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213663 q = 0) : d215417 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213663, d215417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213663, d215417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213664 q = 0) : d215418 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213664, d215418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213664, d215418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213665 q = 0) : d215419 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213665, d215419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213665, d215419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro20862 (p : Pattern) (selected : d213672 p = 0) : d215426 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213636 q = 0) : d215393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213636, d215393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20854 q selected
    | true =>
      simp only [d213636, d215393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20855 q selected
  have h2 (q : Pattern) (selected : d213639 q = 0) : d215307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213639, d215307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20856 q selected
    | true =>
      simp only [d213639, d215307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20857 q selected
  have h3 (q : Pattern) (selected : d213640 q = 0) : d215394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213640, d215394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213640, d215394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213642 q = 0) : d215396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213642, d215396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20858 q selected
    | true =>
      simp only [d213642, d215396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213643 q = 0) : d215397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213643, d215397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213643, d215397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213644 q = 0) : d215398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213644, d215398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213644, d215398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213670 q = 0) : d215424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213670, d215424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213670, d215424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213671 q = 0) : d215425 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213671, d215425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213671, d215425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213672 q = 0) : d215426 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213672, d215426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213672, d215426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20863 (p : Pattern) (selected : d213674 p = 0) : d215428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213660 q = 0) : d215414 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213660, d215414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20826 q selected
    | true =>
      simp only [d213660, d215414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213661 q = 0) : d215415 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213661, d215415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213661, d215415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213662 q = 0) : d215416 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213662, d215416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213662, d215416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213663 q = 0) : d215417 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213663, d215417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213663, d215417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213664 q = 0) : d215418 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213664, d215418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213664, d215418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213674 q = 0) : d215428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213674, d215428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213674, d215428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20864 (p : Pattern) (selected : d213682 p = 0) : d215436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1376 q = 0) : d52864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro407 q selected
  have h2 (q : Pattern) (selected : d1210 q = 0) : d52791 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro407 q selected
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1377 q = 0) : d52865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1211 q = 0) : d52792 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1378 q = 0) : d52866 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d52866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1378, d52866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16649 q = 0) : d127450 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
  have h7 (q : Pattern) (selected : d9753 q = 0) : d101274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
    | true =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16650 q = 0) : d127451 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, d127451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16650, d127451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9755 q = 0) : d101276 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d16651 q = 0) : d127452 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16651, d127452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d16651, d127452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213680 q = 0) : d215434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213680, d215434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213680, d215434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14987 q = 0) : d123112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
  have h13 (q : Pattern) (selected : d9763 q = 0) : d101284 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
    | true =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14988 q = 0) : d123113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14988, d123113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14988, d123113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9765 q = 0) : d101286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d14989 q = 0) : d123114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14989, d123114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d14989, d123114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d14994 q = 0) : d123119 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
  have h18 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d14995 q = 0) : d123120 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9780 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d14996 q = 0) : d123121 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d14996, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213681 q = 0) : d215435 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213681, d215435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213681, d215435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d213682 q = 0) : d215436 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213682, d215436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213682, d215436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20865 (p : Pattern) (selected : d213685 p = 0) : d215439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1380 q = 0) : d52868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro386 q selected
  have h2 (q : Pattern) (selected : d1100 q = 0) : d52681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro386 q selected
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1381 q = 0) : d52869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1101 q = 0) : d52682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1382 q = 0) : d52870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16656 q = 0) : d127457 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
  have h7 (q : Pattern) (selected : d9789 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
    | true =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16657 q = 0) : d127458 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, d127458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16657, d127458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9791 q = 0) : d101312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d16658 q = 0) : d127459 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16658, d127459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d16658, d127459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213683 q = 0) : d215437 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213683, d215437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213683, d215437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14994 q = 0) : d123119 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
  have h13 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14995 q = 0) : d123120 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9780 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d14996 q = 0) : d123121 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d14996, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15004 q = 0) : d123129 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
  have h18 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15005 q = 0) : d123130 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15006 q = 0) : d123131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213684 q = 0) : d215438 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213684, d215438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213684, d215438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d213685 q = 0) : d215439 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213685, d215439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213685, d215439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20866 (p : Pattern) (selected : d213690 p = 0) : d215444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13160 q = 0) : d113452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d113452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13160, d113452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6677 q selected
  have h2 (q : Pattern) (selected : d9814 q = 0) : d101335 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6677 q selected
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13161 q = 0) : d113453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d113453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13161, d113453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9816 q = 0) : d101337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13162 q = 0) : d113454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13162, d113454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13162, d113454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15004 q = 0) : d123129 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
  have h7 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15005 q = 0) : d123130 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15006 q = 0) : d123131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213688 q = 0) : d215442 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213688, d215442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213688, d215442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213689 q = 0) : d215443 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213689, d215443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213689, d215443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213690 q = 0) : d215444 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213690, d215444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213690, d215444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20867 (p : Pattern) (selected : d213695 p = 0) : d215449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1385 q = 0) : d52873 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro387 q selected
  have h2 (q : Pattern) (selected : d1110 q = 0) : d52691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro387 q selected
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1386 q = 0) : d52874 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1111 q = 0) : d52692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1387 q = 0) : d52875 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1391 q = 0) : d52879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
  have h7 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1392 q = 0) : d52880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1393 q = 0) : d52881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213694 q = 0) : d215448 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213694, d215448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213694, d215448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15004 q = 0) : d123129 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
  have h13 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15005 q = 0) : d123130 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15006 q = 0) : d123131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d213689 q = 0) : d215443 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213689, d215443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213689, d215443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d213695 q = 0) : d215449 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213695, d215449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213695, d215449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro20868 (p : Pattern) (selected : d213700 p = 0) : d215454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6350 q = 0) : d76090 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2799 q selected
  have h2 (q : Pattern) (selected : d5018 q = 0) : d69108 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2799 q selected
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6351 q = 0) : d76091 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d76091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6351, d76091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5019 q = 0) : d69109 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6352 q = 0) : d76092 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, d76092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6352, d76092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213698 q = 0) : d215452 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213698, d215452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213698, d215452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15019 q = 0) : d123144 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
  have h8 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15020 q = 0) : d123145 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9846 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15021 q = 0) : d123146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213699 q = 0) : d215453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213699, d215453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213699, d215453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213700 q = 0) : d215454 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213700, d215454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213700, d215454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20869 (p : Pattern) (selected : d213705 p = 0) : d215459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213686 q = 0) : d215440 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213686, d215440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20864 q selected
    | true =>
      simp only [d213686, d215440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20865 q selected
  have h2 (q : Pattern) (selected : d213687 q = 0) : d215441 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213687, d215441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213687, d215441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213691 q = 0) : d215445 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213691, d215445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20865 q selected
    | true =>
      simp only [d213691, d215445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20866 q selected
  have h4 (q : Pattern) (selected : d213692 q = 0) : d215446 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213692, d215446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213692, d215446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213693 q = 0) : d215447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213693, d215447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213693, d215447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213696 q = 0) : d215450 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213696, d215450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20865 q selected
    | true =>
      simp only [d213696, d215450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20867 q selected
  have h7 (q : Pattern) (selected : d213697 q = 0) : d215451 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213697, d215451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213697, d215451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213701 q = 0) : d215455 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213701, d215455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20867 q selected
    | true =>
      simp only [d213701, d215455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20868 q selected
  have h9 (q : Pattern) (selected : d213702 q = 0) : d215456 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213702, d215456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213702, d215456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213703 q = 0) : d215457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213703, d215457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213703, d215457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213704 q = 0) : d215458 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213704, d215458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213704, d215458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213705 q = 0) : d215459 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213705, d215459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213705, d215459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro20870 (p : Pattern) (selected : d213710 p = 0) : d215464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213696 q = 0) : d215450 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213696, d215450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20865 q selected
    | true =>
      simp only [d213696, d215450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20867 q selected
  have h2 (q : Pattern) (selected : d213697 q = 0) : d215451 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213697, d215451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213697, d215451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213701 q = 0) : d215455 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213701, d215455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20867 q selected
    | true =>
      simp only [d213701, d215455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20868 q selected
  have h4 (q : Pattern) (selected : d213702 q = 0) : d215456 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213702, d215456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213702, d215456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213703 q = 0) : d215457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213703, d215457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213703, d215457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213708 q = 0) : d215462 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213708, d215462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213708, d215462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213709 q = 0) : d215463 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213709, d215463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213709, d215463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213710 q = 0) : d215464 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213710, d215464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213710, d215464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20871 (p : Pattern) (selected : d213716 p = 0) : d215470 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213706 q = 0) : d215460 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213706, d215460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20869 q selected
    | true =>
      simp only [d213706, d215460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213707 q = 0) : d215461 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213707, d215461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213707, d215461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213711 q = 0) : d215465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213711, d215465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20870 q selected
    | true =>
      simp only [d213711, d215465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213712 q = 0) : d215466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213712, d215466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213712, d215466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213713 q = 0) : d215467 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213713, d215467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213713, d215467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213714 q = 0) : d215468 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213714, d215468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213714, d215468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213715 q = 0) : d215469 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213715, d215469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213715, d215469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213716 q = 0) : d215470 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213716, d215470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213716, d215470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20872 (p : Pattern) (selected : d213718 p = 0) : d215472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1391 q = 0) : d52879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
  have h2 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1392 q = 0) : d52880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1393 q = 0) : d52881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213717 q = 0) : d215471 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213717, d215471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213717, d215471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15019 q = 0) : d123144 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
  have h8 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15020 q = 0) : d123145 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9846 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15021 q = 0) : d123146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213699 q = 0) : d215453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213699, d215453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213699, d215453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213718 q = 0) : d215472 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213718, d215472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213718, d215472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20873 (p : Pattern) (selected : d213723 p = 0) : d215477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213719 q = 0) : d215473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213719, d215473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20867 q selected
    | true =>
      simp only [d213719, d215473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20872 q selected
  have h2 (q : Pattern) (selected : d213720 q = 0) : d215474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213720, d215474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213720, d215474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213721 q = 0) : d215475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213721, d215475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213721, d215475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213722 q = 0) : d215476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213722, d215476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213722, d215476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213723 q = 0) : d215477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213723, d215477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213723, d215477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20874 (p : Pattern) (selected : d213729 p = 0) : d215483 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213711 q = 0) : d215465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213711, d215465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20870 q selected
    | true =>
      simp only [d213711, d215465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213712 q = 0) : d215466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213712, d215466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213712, d215466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213724 q = 0) : d215478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213724, d215478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20873 q selected
    | true =>
      simp only [d213724, d215478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213725 q = 0) : d215479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213725, d215479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213725, d215479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213726 q = 0) : d215480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213726, d215480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213726, d215480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213727 q = 0) : d215481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213727, d215481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213727, d215481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213728 q = 0) : d215482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213728, d215482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213728, d215482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213729 q = 0) : d215483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213729, d215483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213729, d215483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20875 (p : Pattern) (selected : d213733 p = 0) : d215439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1438 q = 0) : d52868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1438, d52868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1438, d52868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro415 q selected
  have h2 (q : Pattern) (selected : d1255 q = 0) : d52681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1255, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro415 q selected
    | true =>
      simp only [d1255, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1439 q = 0) : d52869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1439, d52869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1439, d52869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1256 q = 0) : d52682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1256, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1256, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1440 q = 0) : d52870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1440, d52870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1440, d52870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16706 q = 0) : d127457 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16706, d127457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16706, d127457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
  have h7 (q : Pattern) (selected : d9896 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
    | true =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16707 q = 0) : d127458 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16707, d127458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16707, d127458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9898 q = 0) : d101312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9898, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9898, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d16708 q = 0) : d127459 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16708, d127459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d16708, d127459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213731 q = 0) : d215437 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213731, d215437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213731, d215437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15057 q = 0) : d123119 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15057, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15057, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
  have h13 (q : Pattern) (selected : d9908 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
    | true =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15058 q = 0) : d123120 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15058, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15058, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9910 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9910, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9910, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15059 q = 0) : d123121 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15059, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15059, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15064 q = 0) : d123129 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15064, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15064, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
  have h18 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15065 q = 0) : d123130 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15065, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15065, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9920 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15066 q = 0) : d123131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15066, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15066, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213732 q = 0) : d215438 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213732, d215438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213732, d215438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d213733 q = 0) : d215439 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213733, d215439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213733, d215439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20876 (p : Pattern) (selected : d213736 p = 0) : d215449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1442 q = 0) : d52873 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1442, d52873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1442, d52873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro416 q selected
  have h2 (q : Pattern) (selected : d1265 q = 0) : d52691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro416 q selected
    | true =>
      simp only [d1265, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1443 q = 0) : d52874 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1443, d52874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1443, d52874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1266 q = 0) : d52692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1266, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1444 q = 0) : d52875 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1444, d52875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1444, d52875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1447 q = 0) : d52879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
  have h7 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1448 q = 0) : d52880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1448, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1277 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1449 q = 0) : d52881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1449, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213734 q = 0) : d215448 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213734, d215448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213734, d215448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15064 q = 0) : d123129 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15064, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15064, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
  have h13 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15065 q = 0) : d123130 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15065, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15065, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9920 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15066 q = 0) : d123131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15066, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15066, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d213735 q = 0) : d215443 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213735, d215443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213735, d215443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d213736 q = 0) : d215449 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213736, d215449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213736, d215449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro20877 (p : Pattern) (selected : d213741 p = 0) : d215454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13209 q = 0) : d76090 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13209, d76090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13209, d76090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6695 q selected
  have h2 (q : Pattern) (selected : d9943 q = 0) : d69108 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6695 q selected
    | true =>
      simp only [d9943, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13210 q = 0) : d76091 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13210, d76091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13210, d76091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9945 q = 0) : d69109 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9945, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9945, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13211 q = 0) : d76092 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13211, d76092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13211, d76092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213739 q = 0) : d215452 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213739, d215452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213739, d215452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15073 q = 0) : d123144 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15073, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15073, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
  have h8 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15074 q = 0) : d123145 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15074, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15074, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9954 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15075 q = 0) : d123146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15075, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15075, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213740 q = 0) : d215453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213740, d215453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213740, d215453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213741 q = 0) : d215454 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213741, d215454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213741, d215454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20878 (p : Pattern) (selected : d213746 p = 0) : d215472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1447 q = 0) : d52879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
  have h2 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1448 q = 0) : d52880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1448, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1277 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1449 q = 0) : d52881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1449, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213745 q = 0) : d215471 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213745, d215471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213745, d215471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15073 q = 0) : d123144 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15073, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15073, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
  have h8 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15074 q = 0) : d123145 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15074, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15074, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9954 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15075 q = 0) : d123146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15075, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15075, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213740 q = 0) : d215453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213740, d215453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213740, d215453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213746 q = 0) : d215472 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213746, d215472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213746, d215472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20879 (p : Pattern) (selected : d213751 p = 0) : d215486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213737 q = 0) : d215450 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213737, d215450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20875 q selected
    | true =>
      simp only [d213737, d215450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20876 q selected
  have h2 (q : Pattern) (selected : d213738 q = 0) : d215451 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213738, d215451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213738, d215451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213742 q = 0) : d215455 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213742, d215455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20876 q selected
    | true =>
      simp only [d213742, d215455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20877 q selected
  have h4 (q : Pattern) (selected : d213743 q = 0) : d215456 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213743, d215456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213743, d215456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213744 q = 0) : d215457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213744, d215457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213744, d215457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213747 q = 0) : d215473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213747, d215473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20876 q selected
    | true =>
      simp only [d213747, d215473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20878 q selected
  have h7 (q : Pattern) (selected : d213748 q = 0) : d215474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213748, d215474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213748, d215474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213749 q = 0) : d215475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213749, d215475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213749, d215475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213750 q = 0) : d215485 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213750, d215485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213750, d215485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213751 q = 0) : d215486 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213751, d215486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213751, d215486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20880 (p : Pattern) (selected : d213755 p = 0) : d215477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213747 q = 0) : d215473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213747, d215473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20876 q selected
    | true =>
      simp only [d213747, d215473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20878 q selected
  have h2 (q : Pattern) (selected : d213748 q = 0) : d215474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213748, d215474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213748, d215474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213749 q = 0) : d215475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213749, d215475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213749, d215475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213754 q = 0) : d215476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213754, d215476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213754, d215476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213755 q = 0) : d215477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213755, d215477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213755, d215477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20881 (p : Pattern) (selected : d213761 p = 0) : d215492 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213752 q = 0) : d215487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213752, d215487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20879 q selected
    | true =>
      simp only [d213752, d215487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213753 q = 0) : d215488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213753, d215488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213753, d215488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213756 q = 0) : d215478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213756, d215478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20880 q selected
    | true =>
      simp only [d213756, d215478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213757 q = 0) : d215479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213757, d215479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213757, d215479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213758 q = 0) : d215489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213758, d215489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213758, d215489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213759 q = 0) : d215490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213759, d215490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213759, d215490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213760 q = 0) : d215491 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213760, d215491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213760, d215491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213761 q = 0) : d215492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213761, d215492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213761, d215492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20882 (p : Pattern) (selected : d213765 p = 0) : d215496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213756 q = 0) : d215478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213756, d215478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20880 q selected
    | true =>
      simp only [d213756, d215478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213757 q = 0) : d215479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213757, d215479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213757, d215479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213762 q = 0) : d215493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213762, d215493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213762, d215493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213763 q = 0) : d215494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213763, d215494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213763, d215494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213764 q = 0) : d215495 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213764, d215495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213764, d215495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213765 q = 0) : d215496 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213765, d215496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213765, d215496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20883 (p : Pattern) (selected : d213768 p = 0) : d215499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1391 q = 0) : d52879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
  have h2 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1392 q = 0) : d52880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1393 q = 0) : d52881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213717 q = 0) : d215471 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213717, d215471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213717, d215471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213768 q = 0) : d215499 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213768, d215499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213768, d215499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro20884 (p : Pattern) (selected : d213773 p = 0) : d215504 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213696 q = 0) : d215450 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213696, d215450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20865 q selected
    | true =>
      simp only [d213696, d215450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20867 q selected
  have h2 (q : Pattern) (selected : d213697 q = 0) : d215451 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213697, d215451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213697, d215451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213701 q = 0) : d215455 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213701, d215455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20867 q selected
    | true =>
      simp only [d213701, d215455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20868 q selected
  have h4 (q : Pattern) (selected : d213702 q = 0) : d215456 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213702, d215456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213702, d215456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213703 q = 0) : d215457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213703, d215457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213703, d215457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213769 q = 0) : d215500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213769, d215500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20867 q selected
    | true =>
      simp only [d213769, d215500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20883 q selected
  have h7 (q : Pattern) (selected : d213770 q = 0) : d215501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213770, d215501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213770, d215501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213771 q = 0) : d215502 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213771, d215502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213771, d215502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213772 q = 0) : d215503 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213772, d215503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213772, d215503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213773 q = 0) : d215504 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213773, d215504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213773, d215504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20885 (p : Pattern) (selected : d213779 p = 0) : d215510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213774 q = 0) : d215505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213774, d215505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20884 q selected
    | true =>
      simp only [d213774, d215505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213775 q = 0) : d215506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213775, d215506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213775, d215506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213776 q = 0) : d215507 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213776, d215507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213776, d215507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213777 q = 0) : d215508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213777, d215508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213777, d215508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213778 q = 0) : d215509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213778, d215509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213778, d215509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213779 q = 0) : d215510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213779, d215510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213779, d215510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20886 (p : Pattern) (selected : d213785 p = 0) : d215516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213730 q = 0) : d215484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213730, d215484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20871 q selected
    | true =>
      simp only [d213730, d215484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20874 q selected
  have h2 (q : Pattern) (selected : d213766 q = 0) : d215497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213766, d215497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20881 q selected
    | true =>
      simp only [d213766, d215497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20882 q selected
  have h3 (q : Pattern) (selected : d213767 q = 0) : d215498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213767, d215498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213767, d215498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213780 q = 0) : d215511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213780, d215511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20885 q selected
    | true =>
      simp only [d213780, d215511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213781 q = 0) : d215512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213781, d215512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213781, d215512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213782 q = 0) : d215513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213782, d215513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213782, d215513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213783 q = 0) : d215514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213783, d215514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213783, d215514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213784 q = 0) : d215515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213784, d215515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213784, d215515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213785 q = 0) : d215516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213785, d215516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213785, d215516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20887 (p : Pattern) (selected : d213790 p = 0) : d215496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213724 q = 0) : d215478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213724, d215478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20873 q selected
    | true =>
      simp only [d213724, d215478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213725 q = 0) : d215479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213725, d215479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213725, d215479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213787 q = 0) : d215493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213787, d215493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213787, d215493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213788 q = 0) : d215494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213788, d215494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213788, d215494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213789 q = 0) : d215495 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213789, d215495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213789, d215495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213790 q = 0) : d215496 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213790, d215496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213790, d215496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20888 (p : Pattern) (selected : d213796 p = 0) : d215523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213791 q = 0) : d215518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213791, d215518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20887 q selected
    | true =>
      simp only [d213791, d215518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213792 q = 0) : d215519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213792, d215519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213792, d215519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213793 q = 0) : d215520 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213793, d215520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213793, d215520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213794 q = 0) : d215521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213794, d215521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213794, d215521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213795 q = 0) : d215522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213795, d215522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213795, d215522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213796 q = 0) : d215523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213796, d215523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213796, d215523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20889 (p : Pattern) (selected : d213802 p = 0) : d215529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213510 q = 0) : d215303 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213510, d215303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213510, d215303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20824 q selected
  have h2 (q : Pattern) (selected : d213511 q = 0) : d215304 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213511, d215304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213511, d215304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d213520 q = 0) : d215313 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213520, d215313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20824 q selected
    | true =>
      simp only [d213520, d215313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20827 q selected
  have h4 (q : Pattern) (selected : d213521 q = 0) : d215314 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213521, d215314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213521, d215314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213522 q = 0) : d215315 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213522, d215315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213522, d215315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213648 q = 0) : d215402 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213648, d215402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20849 q selected
    | true =>
      simp only [d213648, d215402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20859 q selected
  have h7 (q : Pattern) (selected : d213666 q = 0) : d215420 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213666, d215420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20860 q selected
    | true =>
      simp only [d213666, d215420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20861 q selected
  have h8 (q : Pattern) (selected : d213667 q = 0) : d215421 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213667, d215421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213667, d215421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d213668 q = 0) : d215422 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213668, d215422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213668, d215422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d213669 q = 0) : d215423 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213669, d215423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213669, d215423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213673 q = 0) : d215427 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213673, d215427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213673, d215427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20862 q selected
  have h12 (q : Pattern) (selected : d213675 q = 0) : d215429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213675, d215429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213675, d215429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20863 q selected
  have h13 (q : Pattern) (selected : d213676 q = 0) : d215430 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213676, d215430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213676, d215430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213677 q = 0) : d215431 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213677, d215431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d213677, d215431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d213678 q = 0) : d215432 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213678, d215432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d213678, d215432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d213679 q = 0) : d215433 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213679, d215433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213679, d215433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d213786 q = 0) : d215517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213786, d215517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213786, d215517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20886 q selected
  have h18 (q : Pattern) (selected : d213797 q = 0) : d215524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213797, d215524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213797, d215524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20888 q selected
  have h19 (q : Pattern) (selected : d213798 q = 0) : d215525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213798, d215525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d213798, d215525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d213799 q = 0) : d215526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213799, d215526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d213799, d215526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d213800 q = 0) : d215527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d213800, d215527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d213800, d215527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d213801 q = 0) : d215528 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d213801, d215528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d213801, d215528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d213802 q = 0) : d215529 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d213802, d215529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d213802, d215529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20890 (p : Pattern) (selected : d213808 p = 0) : d215535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213803 q = 0) : d215530 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d213803, d215530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213803, d215530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20889 q selected
  have h2 (q : Pattern) (selected : d213804 q = 0) : d215531 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d213804, d215531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213804, d215531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213805 q = 0) : d215532 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d213805, d215532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213805, d215532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213806 q = 0) : d215533 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d213806, d215533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213806, d215533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213807 q = 0) : d215534 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d213807, d215534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213807, d215534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213808 q = 0) : d215535 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d213808, d215535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213808, d215535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20891 (p : Pattern) (selected : d213814 p = 0) : d215541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1555 q = 0) : d52996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1556 q = 0) : d52997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1557 q = 0) : d52998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10074 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
    | true =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10076 q = 0) : d101503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16787 q = 0) : d127561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16787, d127561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16787, d127561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213812 q = 0) : d215539 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213812, d215539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213812, d215539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10065 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15151 q = 0) : d123236 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15156 q = 0) : d123241 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213813 q = 0) : d215540 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213813, d215540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213813, d215540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213814 q = 0) : d215541 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213814, d215541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213814, d215541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20892 (p : Pattern) (selected : d213817 p = 0) : d215544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1570 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1571 q = 0) : d53012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1572 q = 0) : d53013 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10115 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
    | true =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10117 q = 0) : d101544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16792 q = 0) : d127566 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16792, d127566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16792, d127566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213815 q = 0) : d215542 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213815, d215542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213815, d215542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15156 q = 0) : d123241 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213816 q = 0) : d215543 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213816, d215543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213816, d215543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213817 q = 0) : d215544 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213817, d215544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213817, d215544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro20893 (p : Pattern) (selected : d213822 p = 0) : d215549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5134 q = 0) : d69221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2814 q selected
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5135 q = 0) : d69222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5136 q = 0) : d69223 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, d69223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5136, d69223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213820 q = 0) : d215547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213820, d215547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213820, d215547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10135 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10137 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15163 q = 0) : d123248 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213821 q = 0) : d215548 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213821, d215548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213821, d215548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213822 q = 0) : d215549 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213822, d215549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213822, d215549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20894 (p : Pattern) (selected : d213827 p = 0) : d215554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1582 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1583 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1584 q = 0) : d53025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213826 q = 0) : d215553 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213826, d215553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213826, d215553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10135 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10137 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15163 q = 0) : d123248 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213821 q = 0) : d215548 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213821, d215548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213821, d215548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213827 q = 0) : d215554 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213827, d215554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213827, d215554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20895 (p : Pattern) (selected : d213832 p = 0) : d215559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213818 q = 0) : d215545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213818, d215545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20891 q selected
    | true =>
      simp only [d213818, d215545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
  have h2 (q : Pattern) (selected : d213819 q = 0) : d215546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213819, d215546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213819, d215546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213823 q = 0) : d215550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213823, d215550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
    | true =>
      simp only [d213823, d215550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20893 q selected
  have h4 (q : Pattern) (selected : d213824 q = 0) : d215551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213824, d215551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213824, d215551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213825 q = 0) : d215552 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213825, d215552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213825, d215552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213828 q = 0) : d215555 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213828, d215555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
    | true =>
      simp only [d213828, d215555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20894 q selected
  have h7 (q : Pattern) (selected : d213829 q = 0) : d215556 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213829, d215556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213829, d215556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213830 q = 0) : d215557 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213830, d215557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213830, d215557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213831 q = 0) : d215558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213831, d215558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213831, d215558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213832 q = 0) : d215559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213832, d215559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213832, d215559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20896 (p : Pattern) (selected : d213836 p = 0) : d215563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213828 q = 0) : d215555 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213828, d215555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
    | true =>
      simp only [d213828, d215555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20894 q selected
  have h2 (q : Pattern) (selected : d213829 q = 0) : d215556 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213829, d215556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213829, d215556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213830 q = 0) : d215557 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213830, d215557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213830, d215557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213835 q = 0) : d215562 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213835, d215562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213835, d215562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213836 q = 0) : d215563 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213836, d215563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213836, d215563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20897 (p : Pattern) (selected : d213842 p = 0) : d215569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213833 q = 0) : d215560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20895 q selected
    | true =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213834 q = 0) : d215561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213839 q = 0) : d215566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213840 q = 0) : d215567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213840, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213840, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213841 q = 0) : d215568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213841, d215568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213841, d215568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213842 q = 0) : d215569 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213842, d215569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213842, d215569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20898 (p : Pattern) (selected : d213846 p = 0) : d215573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213843 q = 0) : d215570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213844 q = 0) : d215571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213844, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213844, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213845 q = 0) : d215572 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213845, d215572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213845, d215572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213846 q = 0) : d215573 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213846, d215573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213846, d215573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20899 (p : Pattern) (selected : d213852 p = 0) : d215579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213847 q = 0) : d215574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213847, d215574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20897 q selected
    | true =>
      simp only [d213847, d215574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20898 q selected
  have h2 (q : Pattern) (selected : d213848 q = 0) : d215575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213848, d215575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213848, d215575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213849 q = 0) : d215576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213849, d215576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213849, d215576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213850 q = 0) : d215577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213850, d215577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213850, d215577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213851 q = 0) : d215578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213851, d215578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213851, d215578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213852 q = 0) : d215579 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213852, d215579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213852, d215579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20900 (p : Pattern) (selected : d213855 p = 0) : d215582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213833 q = 0) : d215560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20895 q selected
    | true =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213834 q = 0) : d215561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213839 q = 0) : d215566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213840 q = 0) : d215567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213840, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213840, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213841 q = 0) : d215568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213841, d215568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213841, d215568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213855 q = 0) : d215582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213855, d215582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213855, d215582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20901 (p : Pattern) (selected : d213856 p = 0) : d215583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213843 q = 0) : d215570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213844 q = 0) : d215571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213844, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213844, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213845 q = 0) : d215572 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213845, d215572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213845, d215572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213856 q = 0) : d215583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213856, d215583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213856, d215583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20902 (p : Pattern) (selected : d213862 p = 0) : d215589 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213847 q = 0) : d215574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213847, d215574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20897 q selected
    | true =>
      simp only [d213847, d215574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20898 q selected
  have h2 (q : Pattern) (selected : d213848 q = 0) : d215575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213848, d215575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213848, d215575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213849 q = 0) : d215576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213849, d215576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213849, d215576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213850 q = 0) : d215577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213850, d215577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213850, d215577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213851 q = 0) : d215578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213851, d215578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213851, d215578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213857 q = 0) : d215584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213857, d215584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20900 q selected
    | true =>
      simp only [d213857, d215584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20901 q selected
  have h7 (q : Pattern) (selected : d213858 q = 0) : d215585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213858, d215585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213858, d215585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213859 q = 0) : d215586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213859, d215586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213859, d215586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213860 q = 0) : d215587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213860, d215587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213860, d215587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213861 q = 0) : d215588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213861, d215588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213861, d215588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213862 q = 0) : d215589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213862, d215589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213862, d215589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro20903 (p : Pattern) (selected : d213867 p = 0) : d215594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213833 q = 0) : d215560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20895 q selected
    | true =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213834 q = 0) : d215561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213839 q = 0) : d215566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213840 q = 0) : d215567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213840, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213840, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213866 q = 0) : d215593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213866, d215593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213866, d215593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213867 q = 0) : d215594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213867, d215594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213867, d215594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20904 (p : Pattern) (selected : d213869 p = 0) : d215596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213843 q = 0) : d215570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213844 q = 0) : d215571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213844, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213844, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213868 q = 0) : d215595 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213868, d215595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213868, d215595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213869 q = 0) : d215596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213869, d215596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213869, d215596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20905 (p : Pattern) (selected : d213876 p = 0) : d215603 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213833 q = 0) : d215560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20895 q selected
    | true =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213834 q = 0) : d215561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213839 q = 0) : d215566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213874 q = 0) : d215601 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213874, d215601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213874, d215601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213875 q = 0) : d215602 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213875, d215602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213875, d215602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213876 q = 0) : d215603 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213876, d215603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213876, d215603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20906 (p : Pattern) (selected : d213879 p = 0) : d215606 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213843 q = 0) : d215570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213877 q = 0) : d215604 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213877, d215604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213877, d215604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213878 q = 0) : d215605 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213878, d215605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213878, d215605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213879 q = 0) : d215606 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213879, d215606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213879, d215606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20907 (p : Pattern) (selected : d213885 p = 0) : d215612 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1665 q = 0) : d53106 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro487 q selected
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1666 q = 0) : d53107 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1667 q = 0) : d53108 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10036 q = 0) : d101463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10038 q = 0) : d101465 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16859 q = 0) : d127633 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d127633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16859, d127633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213883 q = 0) : d215610 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213883, d215610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213883, d215610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10046 q = 0) : d101473 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10048 q = 0) : d101475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15229 q = 0) : d123314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15229, d123314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15229, d123314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10065 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15151 q = 0) : d123236 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213884 q = 0) : d215611 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213884, d215611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213884, d215611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213885 q = 0) : d215612 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213885, d215612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213885, d215612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20908 (p : Pattern) (selected : d213889 p = 0) : d215616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10099 q = 0) : d101526 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6719 q selected
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10101 q = 0) : d101528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13348 q = 0) : d113608 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, d113608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13348, d113608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15156 q = 0) : d123241 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213888 q = 0) : d215615 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213888, d215615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213888, d215615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213816 q = 0) : d215543 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213816, d215543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213816, d215543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213889 q = 0) : d215616 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213889, d215616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213889, d215616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20909 (p : Pattern) (selected : d213894 p = 0) : d215621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213886 q = 0) : d215613 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213886, d215613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20907 q selected
    | true =>
      simp only [d213886, d215613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20891 q selected
  have h2 (q : Pattern) (selected : d213887 q = 0) : d215614 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213887, d215614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213887, d215614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213890 q = 0) : d215617 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213890, d215617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20891 q selected
    | true =>
      simp only [d213890, d215617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20908 q selected
  have h4 (q : Pattern) (selected : d213891 q = 0) : d215618 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213891, d215618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213891, d215618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213892 q = 0) : d215619 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213892, d215619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213892, d215619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213818 q = 0) : d215545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213818, d215545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20891 q selected
    | true =>
      simp only [d213818, d215545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
  have h7 (q : Pattern) (selected : d213819 q = 0) : d215546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213819, d215546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213819, d215546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213823 q = 0) : d215550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213823, d215550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
    | true =>
      simp only [d213823, d215550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20893 q selected
  have h9 (q : Pattern) (selected : d213824 q = 0) : d215551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213824, d215551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213824, d215551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213825 q = 0) : d215552 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213825, d215552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213825, d215552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213893 q = 0) : d215620 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213893, d215620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213893, d215620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d213894 q = 0) : d215621 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213894, d215621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213894, d215621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro20910 (p : Pattern) (selected : d213899 p = 0) : d215626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213818 q = 0) : d215545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213818, d215545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20891 q selected
    | true =>
      simp only [d213818, d215545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
  have h2 (q : Pattern) (selected : d213819 q = 0) : d215546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213819, d215546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213819, d215546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213823 q = 0) : d215550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213823, d215550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
    | true =>
      simp only [d213823, d215550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20893 q selected
  have h4 (q : Pattern) (selected : d213824 q = 0) : d215551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213824, d215551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213824, d215551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213825 q = 0) : d215552 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213825, d215552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213825, d215552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213897 q = 0) : d215624 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213897, d215624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213897, d215624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213898 q = 0) : d215625 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213898, d215625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213898, d215625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213899 q = 0) : d215626 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213899, d215626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213899, d215626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20911 (p : Pattern) (selected : d213905 p = 0) : d215632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213895 q = 0) : d215622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213895, d215622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20909 q selected
    | true =>
      simp only [d213895, d215622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213896 q = 0) : d215623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213896, d215623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213896, d215623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213900 q = 0) : d215627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213900, d215627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20910 q selected
    | true =>
      simp only [d213900, d215627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213901 q = 0) : d215628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213901, d215628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213901, d215628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213902 q = 0) : d215629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213902, d215629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213902, d215629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213903 q = 0) : d215630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213903, d215630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213903, d215630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213904 q = 0) : d215631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213904, d215631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213904, d215631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213905 q = 0) : d215632 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213905, d215632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213905, d215632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20912 (p : Pattern) (selected : d213909 p = 0) : d215636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213900 q = 0) : d215627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213900, d215627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20910 q selected
    | true =>
      simp only [d213900, d215627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213901 q = 0) : d215628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213901, d215628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213901, d215628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213906 q = 0) : d215633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213906, d215633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213906, d215633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213907 q = 0) : d215634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213907, d215634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213907, d215634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213908 q = 0) : d215635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213908, d215635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213908, d215635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213909 q = 0) : d215636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213909, d215636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213909, d215636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20913 (p : Pattern) (selected : d213913 p = 0) : d215541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1726 q = 0) : d52996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro499 q selected
    | true =>
      simp only [d1726, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1727 q = 0) : d52997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1727, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1727, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1728 q = 0) : d52998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1728, d52998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1728, d52998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10190 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
    | true =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10192 q = 0) : d101503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10192, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10192, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16891 q = 0) : d127561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16891, d127561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16891, d127561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213911 q = 0) : d215539 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213911, d215539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213911, d215539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10200 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
    | true =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10202 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10202, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15261 q = 0) : d123236 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15261, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15261, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10217 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15266 q = 0) : d123241 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15266, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15266, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213912 q = 0) : d215540 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213912, d215540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213912, d215540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213913 q = 0) : d215541 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213913, d215541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213913, d215541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20914 (p : Pattern) (selected : d213916 p = 0) : d215544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1741 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
    | true =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1742 q = 0) : d53012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1742, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1743 q = 0) : d53013 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1743, d53013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1743, d53013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10226 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
    | true =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10228 q = 0) : d101544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10228, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10228, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16896 q = 0) : d127566 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16896, d127566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16896, d127566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213914 q = 0) : d215542 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213914, d215542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213914, d215542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10217 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15266 q = 0) : d123241 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15266, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15266, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213915 q = 0) : d215543 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213915, d215543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213915, d215543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213916 q = 0) : d215544 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213916, d215544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213916, d215544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro20915 (p : Pattern) (selected : d213921 p = 0) : d215549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10243 q = 0) : d69221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6739 q selected
    | true =>
      simp only [d10243, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10245 q = 0) : d69222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10245, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13383 q = 0) : d69223 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13383, d69223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13383, d69223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213919 q = 0) : d215547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213919, d215547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213919, d215547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10255 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10257 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15273 q = 0) : d123248 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15273, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15273, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213920 q = 0) : d215548 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213920, d215548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213920, d215548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213921 q = 0) : d215549 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213921, d215549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213921, d215549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20916 (p : Pattern) (selected : d213926 p = 0) : d215554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1753 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
    | true =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1754 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1755 q = 0) : d53025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1755, d53025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1755, d53025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213925 q = 0) : d215553 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213925, d215553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213925, d215553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10255 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10257 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15273 q = 0) : d123248 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15273, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15273, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213920 q = 0) : d215548 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213920, d215548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213920, d215548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213926 q = 0) : d215554 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213926, d215554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213926, d215554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20917 (p : Pattern) (selected : d213931 p = 0) : d215559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213917 q = 0) : d215545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213917, d215545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20913 q selected
    | true =>
      simp only [d213917, d215545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20914 q selected
  have h2 (q : Pattern) (selected : d213918 q = 0) : d215546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213918, d215546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213918, d215546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213922 q = 0) : d215550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213922, d215550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20914 q selected
    | true =>
      simp only [d213922, d215550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20915 q selected
  have h4 (q : Pattern) (selected : d213923 q = 0) : d215551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213923, d215551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213923, d215551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213924 q = 0) : d215552 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213924, d215552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213924, d215552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213927 q = 0) : d215555 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213927, d215555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20914 q selected
    | true =>
      simp only [d213927, d215555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20916 q selected
  have h7 (q : Pattern) (selected : d213928 q = 0) : d215556 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213928, d215556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213928, d215556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213929 q = 0) : d215557 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213929, d215557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213929, d215557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213930 q = 0) : d215558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213930, d215558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213930, d215558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213931 q = 0) : d215559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213931, d215559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213931, d215559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20918 (p : Pattern) (selected : d213935 p = 0) : d215563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213927 q = 0) : d215555 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213927, d215555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20914 q selected
    | true =>
      simp only [d213927, d215555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20916 q selected
  have h2 (q : Pattern) (selected : d213928 q = 0) : d215556 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213928, d215556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213928, d215556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213929 q = 0) : d215557 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213929, d215557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213929, d215557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213934 q = 0) : d215562 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213934, d215562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213934, d215562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213935 q = 0) : d215563 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213935, d215563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213935, d215563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20919 (p : Pattern) (selected : d213941 p = 0) : d215569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213932 q = 0) : d215560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213932, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20917 q selected
    | true =>
      simp only [d213932, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213933 q = 0) : d215561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213933, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213933, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213936 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213936, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20918 q selected
    | true =>
      simp only [d213936, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213937 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213937, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213937, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213938 q = 0) : d215566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213938, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213938, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213939 q = 0) : d215567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213939, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213939, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213940 q = 0) : d215568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213940, d215568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213940, d215568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213941 q = 0) : d215569 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213941, d215569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213941, d215569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20920 (p : Pattern) (selected : d213945 p = 0) : d215573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213936 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213936, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20918 q selected
    | true =>
      simp only [d213936, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213937 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213937, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213937, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213942 q = 0) : d215570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213942, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213942, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213943 q = 0) : d215571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213943, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213943, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213944 q = 0) : d215572 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213944, d215572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213944, d215572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213945 q = 0) : d215573 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213945, d215573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213945, d215573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20921 (p : Pattern) (selected : d213948 p = 0) : d215639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1582 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1583 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1584 q = 0) : d53025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213826 q = 0) : d215553 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d213826, d215553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213826, d215553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213948 q = 0) : d215639 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d213948, d215639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213948, d215639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20922 (p : Pattern) (selected : d213953 p = 0) : d215644 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213818 q = 0) : d215545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213818, d215545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20891 q selected
    | true =>
      simp only [d213818, d215545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
  have h2 (q : Pattern) (selected : d213819 q = 0) : d215546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213819, d215546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213819, d215546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213823 q = 0) : d215550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213823, d215550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
    | true =>
      simp only [d213823, d215550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20893 q selected
  have h4 (q : Pattern) (selected : d213824 q = 0) : d215551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213824, d215551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213824, d215551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213825 q = 0) : d215552 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213825, d215552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213825, d215552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213949 q = 0) : d215640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d213949, d215640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20892 q selected
    | true =>
      simp only [d213949, d215640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20921 q selected
  have h7 (q : Pattern) (selected : d213950 q = 0) : d215641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d213950, d215641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213950, d215641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213951 q = 0) : d215642 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d213951, d215642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213951, d215642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d213952 q = 0) : d215643 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d213952, d215643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213952, d215643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d213953 q = 0) : d215644 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d213953, d215644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d213953, d215644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20923 (p : Pattern) (selected : d213959 p = 0) : d215650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213954 q = 0) : d215645 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213954, d215645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20922 q selected
    | true =>
      simp only [d213954, d215645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213955 q = 0) : d215646 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213955, d215646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213955, d215646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213956 q = 0) : d215647 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213956, d215647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213956, d215647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213957 q = 0) : d215648 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213957, d215648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213957, d215648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213958 q = 0) : d215649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213958, d215649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213958, d215649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213959 q = 0) : d215650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213959, d215650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213959, d215650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20924 (p : Pattern) (selected : d213965 p = 0) : d215656 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213870 q = 0) : d215597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213870, d215597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20903 q selected
    | true =>
      simp only [d213870, d215597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20904 q selected
  have h2 (q : Pattern) (selected : d213871 q = 0) : d215598 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213871, d215598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213871, d215598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213872 q = 0) : d215599 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213872, d215599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213872, d215599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213873 q = 0) : d215600 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213873, d215600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213873, d215600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213880 q = 0) : d215607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213880, d215607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20905 q selected
    | true =>
      simp only [d213880, d215607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20906 q selected
  have h6 (q : Pattern) (selected : d213881 q = 0) : d215608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213881, d215608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213881, d215608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213882 q = 0) : d215609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213882, d215609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213882, d215609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213910 q = 0) : d215637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213910, d215637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20911 q selected
    | true =>
      simp only [d213910, d215637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20912 q selected
  have h9 (q : Pattern) (selected : d213946 q = 0) : d215574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213946, d215574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20919 q selected
    | true =>
      simp only [d213946, d215574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20920 q selected
  have h10 (q : Pattern) (selected : d213947 q = 0) : d215638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213947, d215638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213947, d215638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213960 q = 0) : d215651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213960, d215651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20923 q selected
    | true =>
      simp only [d213960, d215651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213961 q = 0) : d215652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213961, d215652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213961, d215652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213962 q = 0) : d215653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213962, d215653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213962, d215653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213963 q = 0) : d215654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213963, d215654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213963, d215654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213964 q = 0) : d215655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213964, d215655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213964, d215655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213965 q = 0) : d215656 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213965, d215656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213965, d215656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro20925 (p : Pattern) (selected : d213966 p = 0) : d215657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213833 q = 0) : d215560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20895 q selected
    | true =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213834 q = 0) : d215561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213839 q = 0) : d215566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213840 q = 0) : d215567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213840, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213840, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213866 q = 0) : d215593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213866, d215593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213866, d215593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213966 q = 0) : d215657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213966, d215657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213966, d215657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20926 (p : Pattern) (selected : d213967 p = 0) : d215658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213843 q = 0) : d215570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213844 q = 0) : d215571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213844, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213844, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213868 q = 0) : d215595 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213868, d215595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213868, d215595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213967 q = 0) : d215658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213967, d215658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213967, d215658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20927 (p : Pattern) (selected : d213972 p = 0) : d215663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213833 q = 0) : d215560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20895 q selected
    | true =>
      simp only [d213833, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213834 q = 0) : d215561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213834, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213839 q = 0) : d215566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213839, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213874 q = 0) : d215601 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213874, d215601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213874, d215601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213875 q = 0) : d215602 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213875, d215602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213875, d215602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213972 q = 0) : d215663 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213972, d215663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213972, d215663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20928 (p : Pattern) (selected : d213973 p = 0) : d215664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213843 q = 0) : d215570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213843, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213877 q = 0) : d215604 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213877, d215604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213877, d215604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213878 q = 0) : d215605 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213878, d215605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213878, d215605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213973 q = 0) : d215664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213973, d215664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213973, d215664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20929 (p : Pattern) (selected : d213977 p = 0) : d215668 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213895 q = 0) : d215622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213895, d215622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20909 q selected
    | true =>
      simp only [d213895, d215622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213896 q = 0) : d215623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213896, d215623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213896, d215623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213900 q = 0) : d215627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213900, d215627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20910 q selected
    | true =>
      simp only [d213900, d215627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213901 q = 0) : d215628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213901, d215628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213901, d215628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213902 q = 0) : d215629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213902, d215629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213902, d215629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213903 q = 0) : d215630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213903, d215630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213903, d215630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213904 q = 0) : d215631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213904, d215631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213904, d215631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213977 q = 0) : d215668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213977, d215668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213977, d215668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20930 (p : Pattern) (selected : d213978 p = 0) : d215669 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213900 q = 0) : d215627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213900, d215627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20910 q selected
    | true =>
      simp only [d213900, d215627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213901 q = 0) : d215628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213901, d215628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213901, d215628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213837 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20896 q selected
    | true =>
      simp only [d213837, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213838 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213838, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213906 q = 0) : d215633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213906, d215633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213906, d215633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213907 q = 0) : d215634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213907, d215634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213907, d215634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213908 q = 0) : d215635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213908, d215635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213908, d215635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213978 q = 0) : d215669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213978, d215669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213978, d215669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20931 (p : Pattern) (selected : d213980 p = 0) : d215582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213932 q = 0) : d215560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213932, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20917 q selected
    | true =>
      simp only [d213932, d215560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213933 q = 0) : d215561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213933, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213933, d215561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213936 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213936, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20918 q selected
    | true =>
      simp only [d213936, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213937 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213937, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213937, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213938 q = 0) : d215566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213938, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213938, d215566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213939 q = 0) : d215567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213939, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213939, d215567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213940 q = 0) : d215568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213940, d215568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213940, d215568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213980 q = 0) : d215582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213980, d215582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213980, d215582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20932 (p : Pattern) (selected : d213981 p = 0) : d215583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213936 q = 0) : d215564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213936, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20918 q selected
    | true =>
      simp only [d213936, d215564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213937 q = 0) : d215565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213937, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213937, d215565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213942 q = 0) : d215570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213942, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213942, d215570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213943 q = 0) : d215571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213943, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213943, d215571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213944 q = 0) : d215572 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213944, d215572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213944, d215572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213981 q = 0) : d215583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213981, d215583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213981, d215583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20933 (p : Pattern) (selected : d213984 p = 0) : d215672 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213954 q = 0) : d215645 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d213954, d215645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20922 q selected
    | true =>
      simp only [d213954, d215645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213955 q = 0) : d215646 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d213955, d215646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213955, d215646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213956 q = 0) : d215647 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d213956, d215647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213956, d215647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213957 q = 0) : d215648 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d213957, d215648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213957, d215648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213958 q = 0) : d215649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d213958, d215649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213958, d215649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213984 q = 0) : d215672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d213984, d215672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d213984, d215672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20934 (p : Pattern) (selected : d213990 p = 0) : d215678 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213870 q = 0) : d215597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213870, d215597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20903 q selected
    | true =>
      simp only [d213870, d215597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20904 q selected
  have h2 (q : Pattern) (selected : d213871 q = 0) : d215598 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213871, d215598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213871, d215598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213872 q = 0) : d215599 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213872, d215599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213872, d215599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213873 q = 0) : d215600 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213873, d215600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213873, d215600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213880 q = 0) : d215607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213880, d215607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20905 q selected
    | true =>
      simp only [d213880, d215607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20906 q selected
  have h6 (q : Pattern) (selected : d213881 q = 0) : d215608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213881, d215608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213881, d215608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d213882 q = 0) : d215609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213882, d215609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d213882, d215609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d213910 q = 0) : d215637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213910, d215637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20911 q selected
    | true =>
      simp only [d213910, d215637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20912 q selected
  have h9 (q : Pattern) (selected : d213946 q = 0) : d215574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213946, d215574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20919 q selected
    | true =>
      simp only [d213946, d215574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20920 q selected
  have h10 (q : Pattern) (selected : d213947 q = 0) : d215638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213947, d215638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d213947, d215638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d213960 q = 0) : d215651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213960, d215651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20923 q selected
    | true =>
      simp only [d213960, d215651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d213961 q = 0) : d215652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213961, d215652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d213961, d215652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d213962 q = 0) : d215653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213962, d215653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d213962, d215653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d213963 q = 0) : d215654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213963, d215654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213963, d215654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d213964 q = 0) : d215655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213964, d215655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213964, d215655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d213968 q = 0) : d215659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213968, d215659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20925 q selected
    | true =>
      simp only [d213968, d215659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20926 q selected
  have h17 (q : Pattern) (selected : d213969 q = 0) : d215660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213969, d215660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213969, d215660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d213970 q = 0) : d215661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213970, d215661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d213970, d215661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d213971 q = 0) : d215662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213971, d215662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213971, d215662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d213974 q = 0) : d215665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213974, d215665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20927 q selected
    | true =>
      simp only [d213974, d215665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20928 q selected
  have h21 (q : Pattern) (selected : d213975 q = 0) : d215666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213975, d215666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213975, d215666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d213976 q = 0) : d215667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213976, d215667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d213976, d215667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d213979 q = 0) : d215670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213979, d215670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20929 q selected
    | true =>
      simp only [d213979, d215670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20930 q selected
  have h24 (q : Pattern) (selected : d213982 q = 0) : d215584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213982, d215584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20931 q selected
    | true =>
      simp only [d213982, d215584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20932 q selected
  have h25 (q : Pattern) (selected : d213983 q = 0) : d215671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213983, d215671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d213983, d215671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d213985 q = 0) : d215673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213985, d215673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20933 q selected
    | true =>
      simp only [d213985, d215673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d213986 q = 0) : d215674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213986, d215674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d213986, d215674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d213987 q = 0) : d215675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213987, d215675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d213987, d215675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d213988 q = 0) : d215676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213988, d215676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d213988, d215676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d213989 q = 0) : d215677 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213989, d215677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d213989, d215677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d213990 q = 0) : d215678 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213990, d215678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d213990, d215678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro20935 (p : Pattern) (selected : d214002 p = 0) : d215690 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213992 q = 0) : d215680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213992, d215680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20912 q selected
    | true =>
      simp only [d213992, d215680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20898 q selected
  have h2 (q : Pattern) (selected : d213993 q = 0) : d215681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213993, d215681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213993, d215681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213994 q = 0) : d215682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213994, d215682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213994, d215682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d213995 q = 0) : d215683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d213995, d215683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213995, d215683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d213996 q = 0) : d215684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d213996, d215684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213996, d215684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213997 q = 0) : d215685 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213997, d215685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20898 q selected
    | true =>
      simp only [d213997, d215685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d213998 q = 0) : d215686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213998, d215686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213998, d215686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d213999 q = 0) : d215687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213999, d215687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d213999, d215687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214000 q = 0) : d215688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214000, d215688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214000, d215688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214001 q = 0) : d215689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214001, d215689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214001, d215689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214002 q = 0) : d215690 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214002, d215690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214002, d215690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro20936 (p : Pattern) (selected : d214008 p = 0) : d215696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213997 q = 0) : d215685 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213997, d215685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20898 q selected
    | true =>
      simp only [d213997, d215685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d213998 q = 0) : d215686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213998, d215686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213998, d215686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d213999 q = 0) : d215687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213999, d215687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213999, d215687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214000 q = 0) : d215688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214000, d215688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214000, d215688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214001 q = 0) : d215689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214001, d215689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214001, d215689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214003 q = 0) : d215691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214003, d215691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20901 q selected
    | true =>
      simp only [d214003, d215691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214004 q = 0) : d215692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214004, d215692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214004, d215692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214005 q = 0) : d215693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214005, d215693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214005, d215693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214006 q = 0) : d215694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214006, d215694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214006, d215694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214007 q = 0) : d215695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214007, d215695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214007, d215695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214008 q = 0) : d215696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214008, d215696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214008, d215696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro20937 (p : Pattern) (selected : d214015 p = 0) : d215703 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213979 q = 0) : d215670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213979, d215670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20929 q selected
    | true =>
      simp only [d213979, d215670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20930 q selected
  have h2 (q : Pattern) (selected : d213982 q = 0) : d215584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213982, d215584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20931 q selected
    | true =>
      simp only [d213982, d215584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20932 q selected
  have h3 (q : Pattern) (selected : d213983 q = 0) : d215671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213983, d215671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213983, d215671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d213985 q = 0) : d215673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d213985, d215673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20933 q selected
    | true =>
      simp only [d213985, d215673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213986 q = 0) : d215674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d213986, d215674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d213986, d215674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d213987 q = 0) : d215675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d213987, d215675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213987, d215675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214013 q = 0) : d215701 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214013, d215701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214013, d215701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214014 q = 0) : d215702 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214014, d215702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214014, d215702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d214015 q = 0) : d215703 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214015, d215703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214015, d215703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20938 (p : Pattern) (selected : d214017 p = 0) : d215705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214003 q = 0) : d215691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214003, d215691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20901 q selected
    | true =>
      simp only [d214003, d215691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214004 q = 0) : d215692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214004, d215692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214004, d215692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214005 q = 0) : d215693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214005, d215693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214005, d215693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214006 q = 0) : d215694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214006, d215694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214006, d215694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214007 q = 0) : d215695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214007, d215695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214007, d215695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214017 q = 0) : d215705 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214017, d215705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214017, d215705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20939 (p : Pattern) (selected : d214025 p = 0) : d215713 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1853 q = 0) : d53179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro487 q selected
  have h2 (q : Pattern) (selected : d1665 q = 0) : d53106 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro487 q selected
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1854 q = 0) : d53180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1666 q = 0) : d53107 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1855 q = 0) : d53181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d53181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1855, d53181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17004 q = 0) : d127738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
  have h7 (q : Pattern) (selected : d10036 q = 0) : d101463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17005 q = 0) : d127739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10038 q = 0) : d101465 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17006 q = 0) : d127740 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214023 q = 0) : d215711 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214023, d215711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214023, d215711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15380 q = 0) : d123419 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
  have h13 (q : Pattern) (selected : d10046 q = 0) : d101473 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15381 q = 0) : d123420 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d123420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15381, d123420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10048 q = 0) : d101475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15382 q = 0) : d123421 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d123421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15382, d123421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15387 q = 0) : d123426 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
  have h18 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15388 q = 0) : d123427 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10065 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15389 q = 0) : d123428 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15389, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d214024 q = 0) : d215712 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214024, d215712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214024, d215712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d214025 q = 0) : d215713 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214025, d215713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214025, d215713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20940 (p : Pattern) (selected : d214028 p = 0) : d215716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1857 q = 0) : d53183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
  have h2 (q : Pattern) (selected : d1555 q = 0) : d52996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1858 q = 0) : d53184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1556 q = 0) : d52997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1859 q = 0) : d53185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17011 q = 0) : d127745 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
  have h7 (q : Pattern) (selected : d10074 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
    | true =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17012 q = 0) : d127746 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, d127746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17012, d127746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10076 q = 0) : d101503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17013 q = 0) : d127747 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17013, d127747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17013, d127747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214026 q = 0) : d215714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214026, d215714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214026, d215714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15387 q = 0) : d123426 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
  have h13 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15388 q = 0) : d123427 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10065 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15389 q = 0) : d123428 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15389, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15397 q = 0) : d123436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
  have h18 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15398 q = 0) : d123437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15399 q = 0) : d123438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d214027 q = 0) : d215715 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214027, d215715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214027, d215715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d214028 q = 0) : d215716 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214028, d215716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214028, d215716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20941 (p : Pattern) (selected : d214033 p = 0) : d215721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13486 q = 0) : d113708 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6719 q selected
  have h2 (q : Pattern) (selected : d10099 q = 0) : d101526 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6719 q selected
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13487 q = 0) : d113709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d113709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13487, d113709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10101 q = 0) : d101528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13488 q = 0) : d113710 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, d113710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13488, d113710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15397 q = 0) : d123436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
  have h7 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15398 q = 0) : d123437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15399 q = 0) : d123438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214031 q = 0) : d215719 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214031, d215719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214031, d215719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214032 q = 0) : d215720 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214032, d215720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214032, d215720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214033 q = 0) : d215721 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214033, d215721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214033, d215721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20942 (p : Pattern) (selected : d214038 p = 0) : d215726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1862 q = 0) : d53188 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
  have h2 (q : Pattern) (selected : d1570 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1863 q = 0) : d53189 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1571 q = 0) : d53012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1864 q = 0) : d53190 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17027 q = 0) : d127761 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
  have h7 (q : Pattern) (selected : d10115 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
    | true =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17028 q = 0) : d127762 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d127762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17028, d127762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10117 q = 0) : d101544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17029 q = 0) : d127763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17029, d127763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17029, d127763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214037 q = 0) : d215725 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214037, d215725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214037, d215725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15397 q = 0) : d123436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
  have h13 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15398 q = 0) : d123437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15399 q = 0) : d123438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d214032 q = 0) : d215720 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214032, d215720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214032, d215720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d214038 q = 0) : d215726 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214038, d215726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214038, d215726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro20943 (p : Pattern) (selected : d214043 p = 0) : d215731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6496 q = 0) : d76225 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2814 q selected
  have h2 (q : Pattern) (selected : d5134 q = 0) : d69221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2814 q selected
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6497 q = 0) : d76226 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d76226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6497, d76226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5135 q = 0) : d69222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6498 q = 0) : d76227 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, d76227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6498, d76227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214041 q = 0) : d215729 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214041, d215729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214041, d215729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15412 q = 0) : d123451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
  have h8 (q : Pattern) (selected : d10135 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15413 q = 0) : d123452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10137 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15414 q = 0) : d123453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214042 q = 0) : d215730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214042, d215730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214042, d215730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214043 q = 0) : d215731 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214043, d215731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214043, d215731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20944 (p : Pattern) (selected : d214048 p = 0) : d215736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214029 q = 0) : d215717 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214029, d215717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20939 q selected
    | true =>
      simp only [d214029, d215717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20940 q selected
  have h2 (q : Pattern) (selected : d214030 q = 0) : d215718 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214030, d215718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214030, d215718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214034 q = 0) : d215722 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214034, d215722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20940 q selected
    | true =>
      simp only [d214034, d215722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20941 q selected
  have h4 (q : Pattern) (selected : d214035 q = 0) : d215723 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214035, d215723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214035, d215723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214036 q = 0) : d215724 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214036, d215724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214036, d215724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214039 q = 0) : d215727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214039, d215727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20940 q selected
    | true =>
      simp only [d214039, d215727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20942 q selected
  have h7 (q : Pattern) (selected : d214040 q = 0) : d215728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214040, d215728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214040, d215728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214044 q = 0) : d215732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214044, d215732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20942 q selected
    | true =>
      simp only [d214044, d215732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20943 q selected
  have h9 (q : Pattern) (selected : d214045 q = 0) : d215733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214045, d215733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214045, d215733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214046 q = 0) : d215734 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214046, d215734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214046, d215734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214047 q = 0) : d215735 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214047, d215735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214047, d215735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214048 q = 0) : d215736 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214048, d215736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214048, d215736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro20945 (p : Pattern) (selected : d214053 p = 0) : d215741 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214039 q = 0) : d215727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214039, d215727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20940 q selected
    | true =>
      simp only [d214039, d215727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20942 q selected
  have h2 (q : Pattern) (selected : d214040 q = 0) : d215728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214040, d215728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214040, d215728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214044 q = 0) : d215732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214044, d215732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20942 q selected
    | true =>
      simp only [d214044, d215732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20943 q selected
  have h4 (q : Pattern) (selected : d214045 q = 0) : d215733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214045, d215733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214045, d215733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214046 q = 0) : d215734 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214046, d215734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214046, d215734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214051 q = 0) : d215739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214051, d215739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214051, d215739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214052 q = 0) : d215740 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214052, d215740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214052, d215740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214053 q = 0) : d215741 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214053, d215741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214053, d215741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20946 (p : Pattern) (selected : d214059 p = 0) : d215747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214049 q = 0) : d215737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214049, d215737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20944 q selected
    | true =>
      simp only [d214049, d215737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214050 q = 0) : d215738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214050, d215738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214050, d215738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214054 q = 0) : d215742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214054, d215742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20945 q selected
    | true =>
      simp only [d214054, d215742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214055 q = 0) : d215743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214055, d215743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214055, d215743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214056 q = 0) : d215744 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214056, d215744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214056, d215744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214057 q = 0) : d215745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214057, d215745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214057, d215745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214058 q = 0) : d215746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214058, d215746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214058, d215746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214059 q = 0) : d215747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214059, d215747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214059, d215747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20947 (p : Pattern) (selected : d214061 p = 0) : d215749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1868 q = 0) : d53194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
  have h2 (q : Pattern) (selected : d1582 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1869 q = 0) : d53195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1583 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1870 q = 0) : d53196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214060 q = 0) : d215748 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214060, d215748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214060, d215748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15412 q = 0) : d123451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
  have h8 (q : Pattern) (selected : d10135 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15413 q = 0) : d123452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10137 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15414 q = 0) : d123453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214042 q = 0) : d215730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214042, d215730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214042, d215730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214061 q = 0) : d215749 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214061, d215749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214061, d215749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20948 (p : Pattern) (selected : d214066 p = 0) : d215754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214062 q = 0) : d215750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214062, d215750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20942 q selected
    | true =>
      simp only [d214062, d215750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20947 q selected
  have h2 (q : Pattern) (selected : d214063 q = 0) : d215751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214063, d215751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214063, d215751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214064 q = 0) : d215752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214064, d215752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214064, d215752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214065 q = 0) : d215753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214065, d215753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214065, d215753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214066 q = 0) : d215754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214066, d215754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214066, d215754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20949 (p : Pattern) (selected : d214072 p = 0) : d215760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214054 q = 0) : d215742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214054, d215742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20945 q selected
    | true =>
      simp only [d214054, d215742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214055 q = 0) : d215743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214055, d215743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214055, d215743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214067 q = 0) : d215755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214067, d215755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20948 q selected
    | true =>
      simp only [d214067, d215755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214068 q = 0) : d215756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214068, d215756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214068, d215756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214069 q = 0) : d215757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214069, d215757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214069, d215757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214070 q = 0) : d215758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214070, d215758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214070, d215758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214071 q = 0) : d215759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214071, d215759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214071, d215759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214072 q = 0) : d215760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214072, d215760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214072, d215760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20950 (p : Pattern) (selected : d214076 p = 0) : d215716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1915 q = 0) : d53183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1915, d53183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1915, d53183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro499 q selected
  have h2 (q : Pattern) (selected : d1726 q = 0) : d52996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro499 q selected
    | true =>
      simp only [d1726, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1916 q = 0) : d53184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1916, d53184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1916, d53184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1727 q = 0) : d52997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1727, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1727, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1917 q = 0) : d53185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1917, d53185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1917, d53185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17066 q = 0) : d127745 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17066, d127745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17066, d127745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
  have h7 (q : Pattern) (selected : d10190 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
    | true =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17067 q = 0) : d127746 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17067, d127746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17067, d127746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10192 q = 0) : d101503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10192, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10192, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17068 q = 0) : d127747 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17068, d127747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17068, d127747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214074 q = 0) : d215714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214074, d215714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214074, d215714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15450 q = 0) : d123426 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15450, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15450, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
  have h13 (q : Pattern) (selected : d10200 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
    | true =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15451 q = 0) : d123427 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15451, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15451, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10202 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10202, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15452 q = 0) : d123428 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15452, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15452, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15457 q = 0) : d123436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
  have h18 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15458 q = 0) : d123437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15458, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10217 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15459 q = 0) : d123438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15459, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15459, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d214075 q = 0) : d215715 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214075, d215715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214075, d215715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d214076 q = 0) : d215716 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214076, d215716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214076, d215716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20951 (p : Pattern) (selected : d214079 p = 0) : d215726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1919 q = 0) : d53188 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1919, d53188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1919, d53188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
  have h2 (q : Pattern) (selected : d1741 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
    | true =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1920 q = 0) : d53189 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1920, d53189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1920, d53189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1742 q = 0) : d53012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1742, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1921 q = 0) : d53190 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1921, d53190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1921, d53190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17073 q = 0) : d127761 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17073, d127761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17073, d127761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
  have h7 (q : Pattern) (selected : d10226 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
    | true =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17074 q = 0) : d127762 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17074, d127762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17074, d127762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10228 q = 0) : d101544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10228, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10228, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17075 q = 0) : d127763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17075, d127763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17075, d127763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214077 q = 0) : d215725 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214077, d215725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214077, d215725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15457 q = 0) : d123436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
  have h13 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15458 q = 0) : d123437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15458, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10217 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15459 q = 0) : d123438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15459, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15459, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d214078 q = 0) : d215720 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214078, d215720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214078, d215720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d214079 q = 0) : d215726 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214079, d215726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214079, d215726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro20952 (p : Pattern) (selected : d214084 p = 0) : d215731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13535 q = 0) : d76225 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13535, d76225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13535, d76225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6739 q selected
  have h2 (q : Pattern) (selected : d10243 q = 0) : d69221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6739 q selected
    | true =>
      simp only [d10243, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13536 q = 0) : d76226 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13536, d76226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13536, d76226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10245 q = 0) : d69222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10245, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13537 q = 0) : d76227 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13537, d76227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13537, d76227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214082 q = 0) : d215729 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214082, d215729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214082, d215729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15466 q = 0) : d123451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15466, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15466, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
  have h8 (q : Pattern) (selected : d10255 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15467 q = 0) : d123452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15467, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15467, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10257 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15468 q = 0) : d123453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15468, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15468, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214083 q = 0) : d215730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214083, d215730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214083, d215730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214084 q = 0) : d215731 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214084, d215731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214084, d215731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20953 (p : Pattern) (selected : d214089 p = 0) : d215749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1924 q = 0) : d53194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
  have h2 (q : Pattern) (selected : d1753 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
    | true =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1925 q = 0) : d53195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1925, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1754 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1926 q = 0) : d53196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1926, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1926, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214088 q = 0) : d215748 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214088, d215748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214088, d215748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15466 q = 0) : d123451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15466, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15466, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
  have h8 (q : Pattern) (selected : d10255 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15467 q = 0) : d123452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15467, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15467, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10257 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15468 q = 0) : d123453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15468, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15468, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214083 q = 0) : d215730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214083, d215730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214083, d215730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214089 q = 0) : d215749 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214089, d215749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214089, d215749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro20954 (p : Pattern) (selected : d214094 p = 0) : d215763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214080 q = 0) : d215727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214080, d215727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20950 q selected
    | true =>
      simp only [d214080, d215727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20951 q selected
  have h2 (q : Pattern) (selected : d214081 q = 0) : d215728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214081, d215728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214081, d215728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214085 q = 0) : d215732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214085, d215732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20951 q selected
    | true =>
      simp only [d214085, d215732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20952 q selected
  have h4 (q : Pattern) (selected : d214086 q = 0) : d215733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214086, d215733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214086, d215733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214087 q = 0) : d215734 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214087, d215734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214087, d215734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214090 q = 0) : d215750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214090, d215750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20951 q selected
    | true =>
      simp only [d214090, d215750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20953 q selected
  have h7 (q : Pattern) (selected : d214091 q = 0) : d215751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214091, d215751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214091, d215751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214092 q = 0) : d215752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214092, d215752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214092, d215752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214093 q = 0) : d215762 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214093, d215762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214093, d215762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214094 q = 0) : d215763 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214094, d215763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214094, d215763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20955 (p : Pattern) (selected : d214098 p = 0) : d215754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214090 q = 0) : d215750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214090, d215750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20951 q selected
    | true =>
      simp only [d214090, d215750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20953 q selected
  have h2 (q : Pattern) (selected : d214091 q = 0) : d215751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214091, d215751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214091, d215751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214092 q = 0) : d215752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214092, d215752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214092, d215752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214097 q = 0) : d215753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214097, d215753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214097, d215753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214098 q = 0) : d215754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214098, d215754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214098, d215754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20956 (p : Pattern) (selected : d214104 p = 0) : d215769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214095 q = 0) : d215764 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214095, d215764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20954 q selected
    | true =>
      simp only [d214095, d215764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214096 q = 0) : d215765 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214096, d215765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214096, d215765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214099 q = 0) : d215755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214099, d215755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20955 q selected
    | true =>
      simp only [d214099, d215755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214100 q = 0) : d215756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214100, d215756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214100, d215756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214101 q = 0) : d215766 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214101, d215766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214101, d215766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214102 q = 0) : d215767 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214102, d215767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214102, d215767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214103 q = 0) : d215768 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214103, d215768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214103, d215768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214104 q = 0) : d215769 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214104, d215769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214104, d215769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20957 (p : Pattern) (selected : d214108 p = 0) : d215773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214099 q = 0) : d215755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214099, d215755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20955 q selected
    | true =>
      simp only [d214099, d215755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214100 q = 0) : d215756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214100, d215756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214100, d215756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214105 q = 0) : d215770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214105, d215770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214105, d215770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214106 q = 0) : d215771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214106, d215771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214106, d215771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214107 q = 0) : d215772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214107, d215772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214107, d215772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214108 q = 0) : d215773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214108, d215773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214108, d215773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20958 (p : Pattern) (selected : d214111 p = 0) : d215776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1868 q = 0) : d53194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
  have h2 (q : Pattern) (selected : d1582 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1869 q = 0) : d53195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1583 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1870 q = 0) : d53196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214060 q = 0) : d215748 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214060, d215748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214060, d215748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214111 q = 0) : d215776 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214111, d215776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214111, d215776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro20959 (p : Pattern) (selected : d214116 p = 0) : d215781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214039 q = 0) : d215727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214039, d215727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20940 q selected
    | true =>
      simp only [d214039, d215727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20942 q selected
  have h2 (q : Pattern) (selected : d214040 q = 0) : d215728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214040, d215728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214040, d215728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214044 q = 0) : d215732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214044, d215732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20942 q selected
    | true =>
      simp only [d214044, d215732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20943 q selected
  have h4 (q : Pattern) (selected : d214045 q = 0) : d215733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214045, d215733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214045, d215733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214046 q = 0) : d215734 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214046, d215734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214046, d215734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214112 q = 0) : d215777 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214112, d215777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20942 q selected
    | true =>
      simp only [d214112, d215777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20958 q selected
  have h7 (q : Pattern) (selected : d214113 q = 0) : d215778 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214113, d215778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214113, d215778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214114 q = 0) : d215779 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214114, d215779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214114, d215779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214115 q = 0) : d215780 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214115, d215780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214115, d215780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214116 q = 0) : d215781 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214116, d215781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214116, d215781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20960 (p : Pattern) (selected : d214122 p = 0) : d215787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214117 q = 0) : d215782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214117, d215782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20959 q selected
    | true =>
      simp only [d214117, d215782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214118 q = 0) : d215783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214118, d215783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214118, d215783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214119 q = 0) : d215784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214119, d215784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214119, d215784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214120 q = 0) : d215785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214120, d215785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214120, d215785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214121 q = 0) : d215786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214121, d215786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214121, d215786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214122 q = 0) : d215787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214122, d215787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214122, d215787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20961 (p : Pattern) (selected : d214128 p = 0) : d215793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214073 q = 0) : d215761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214073, d215761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20946 q selected
    | true =>
      simp only [d214073, d215761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20949 q selected
  have h2 (q : Pattern) (selected : d214109 q = 0) : d215774 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214109, d215774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20956 q selected
    | true =>
      simp only [d214109, d215774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20957 q selected
  have h3 (q : Pattern) (selected : d214110 q = 0) : d215775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214110, d215775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d214110, d215775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214123 q = 0) : d215788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214123, d215788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20960 q selected
    | true =>
      simp only [d214123, d215788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214124 q = 0) : d215789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214124, d215789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214124, d215789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214125 q = 0) : d215790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214125, d215790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214125, d215790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214126 q = 0) : d215791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214126, d215791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214126, d215791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214127 q = 0) : d215792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214127, d215792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214127, d215792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d214128 q = 0) : d215793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214128, d215793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214128, d215793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20962 (p : Pattern) (selected : d214133 p = 0) : d215773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214067 q = 0) : d215755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214067, d215755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20948 q selected
    | true =>
      simp only [d214067, d215755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214068 q = 0) : d215756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214068, d215756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214068, d215756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214130 q = 0) : d215770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214130, d215770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214130, d215770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214131 q = 0) : d215771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214131, d215771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214131, d215771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214132 q = 0) : d215772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214132, d215772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214132, d215772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214133 q = 0) : d215773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214133, d215773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214133, d215773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20963 (p : Pattern) (selected : d214139 p = 0) : d215800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214134 q = 0) : d215795 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214134, d215795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20962 q selected
    | true =>
      simp only [d214134, d215795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214135 q = 0) : d215796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214135, d215796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214135, d215796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214136 q = 0) : d215797 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214136, d215797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214136, d215797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214137 q = 0) : d215798 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214137, d215798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214137, d215798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214138 q = 0) : d215799 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214138, d215799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214138, d215799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214139 q = 0) : d215800 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214139, d215800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214139, d215800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20964 (p : Pattern) (selected : d214145 p = 0) : d215806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d213853 q = 0) : d215580 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213853, d215580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d213853, d215580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20899 q selected
  have h2 (q : Pattern) (selected : d213854 q = 0) : d215581 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213854, d215581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d213854, d215581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d213863 q = 0) : d215590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213863, d215590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20899 q selected
    | true =>
      simp only [d213863, d215590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20902 q selected
  have h4 (q : Pattern) (selected : d213864 q = 0) : d215591 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d213864, d215591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d213864, d215591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d213865 q = 0) : d215592 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d213865, d215592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d213865, d215592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d213991 q = 0) : d215679 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d213991, d215679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20924 q selected
    | true =>
      simp only [d213991, d215679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20934 q selected
  have h7 (q : Pattern) (selected : d214009 q = 0) : d215697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214009, d215697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20935 q selected
    | true =>
      simp only [d214009, d215697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20936 q selected
  have h8 (q : Pattern) (selected : d214010 q = 0) : d215698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214010, d215698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214010, d215698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d214011 q = 0) : d215699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214011, d215699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d214011, d215699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d214012 q = 0) : d215700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214012, d215700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214012, d215700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214016 q = 0) : d215704 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214016, d215704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214016, d215704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20937 q selected
  have h12 (q : Pattern) (selected : d214018 q = 0) : d215706 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214018, d215706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214018, d215706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20938 q selected
  have h13 (q : Pattern) (selected : d214019 q = 0) : d215707 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214019, d215707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214019, d215707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d214020 q = 0) : d215708 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214020, d215708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d214020, d215708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d214021 q = 0) : d215709 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214021, d215709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d214021, d215709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d214022 q = 0) : d215710 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d214022, d215710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214022, d215710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d214129 q = 0) : d215794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214129, d215794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214129, d215794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20961 q selected
  have h18 (q : Pattern) (selected : d214140 q = 0) : d215801 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214140, d215801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214140, d215801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20963 q selected
  have h19 (q : Pattern) (selected : d214141 q = 0) : d215802 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d214141, d215802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d214141, d215802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d214142 q = 0) : d215803 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d214142, d215803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d214142, d215803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d214143 q = 0) : d215804 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d214143, d215804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d214143, d215804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d214144 q = 0) : d215805 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d214144, d215805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d214144, d215805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d214145 q = 0) : d215806 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d214145, d215806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d214145, d215806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro20965 (p : Pattern) (selected : d214151 p = 0) : d215812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214146 q = 0) : d215807 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d214146, d215807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214146, d215807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20964 q selected
  have h2 (q : Pattern) (selected : d214147 q = 0) : d215808 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d214147, d215808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214147, d215808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214148 q = 0) : d215809 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d214148, d215809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214148, d215809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214149 q = 0) : d215810 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d214149, d215810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214149, d215810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214150 q = 0) : d215811 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d214150, d215811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214150, d215811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214151 q = 0) : d215812 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d214151, d215812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214151, d215812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20966 (p : Pattern) (selected : d214158 p = 0) : d215819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2035 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2036 q = 0) : d53315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2037 q = 0) : d53316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10364 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10366 q = 0) : d101687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17153 q = 0) : d127855 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214156 q = 0) : d215817 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214156, d215817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214156, d215817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d13675 q = 0) : d113865 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15548 q = 0) : d123547 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d214157 q = 0) : d215818 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214157, d215818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214157, d215818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d214158 q = 0) : d215819 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214158, d215819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214158, d215819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20967 (p : Pattern) (selected : d214161 p = 0) : d215822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2053 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2054 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2055 q = 0) : d53334 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10391 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
    | true =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10393 q = 0) : d101714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17158 q = 0) : d127860 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17158, d127860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17158, d127860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214159 q = 0) : d215820 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214159, d215820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214159, d215820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15548 q = 0) : d123547 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214160 q = 0) : d215821 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214160, d215821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214160, d215821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d214161 q = 0) : d215822 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214161, d215822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214161, d215822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro20968 (p : Pattern) (selected : d214166 p = 0) : d215827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5247 q = 0) : d69331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2828 q selected
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5248 q = 0) : d69332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5249 q = 0) : d69333 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5249, d69333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5249, d69333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214164 q = 0) : d215825 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214164, d215825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214164, d215825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10412 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10414 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15555 q = 0) : d123554 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214165 q = 0) : d215826 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214165, d215826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214165, d215826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214166 q = 0) : d215827 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214166, d215827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214166, d215827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20969 (p : Pattern) (selected : d214171 p = 0) : d215832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2067 q = 0) : d53346 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214170 q = 0) : d215831 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214170, d215831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214170, d215831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10412 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10414 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15555 q = 0) : d123554 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214165 q = 0) : d215826 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214165, d215826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214165, d215826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214171 q = 0) : d215832 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214171, d215832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214171, d215832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20970 (p : Pattern) (selected : d214176 p = 0) : d215837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214162 q = 0) : d215823 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214162, d215823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20966 q selected
    | true =>
      simp only [d214162, d215823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
  have h2 (q : Pattern) (selected : d214163 q = 0) : d215824 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214163, d215824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214163, d215824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214167 q = 0) : d215828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214167, d215828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
    | true =>
      simp only [d214167, d215828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20968 q selected
  have h4 (q : Pattern) (selected : d214168 q = 0) : d215829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214168, d215829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214168, d215829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214169 q = 0) : d215830 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214169, d215830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214169, d215830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214172 q = 0) : d215833 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214172, d215833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
    | true =>
      simp only [d214172, d215833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20969 q selected
  have h7 (q : Pattern) (selected : d214173 q = 0) : d215834 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214173, d215834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214173, d215834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214174 q = 0) : d215835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214174, d215835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214174, d215835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214175 q = 0) : d215836 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214175, d215836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214175, d215836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214176 q = 0) : d215837 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214176, d215837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214176, d215837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20971 (p : Pattern) (selected : d214180 p = 0) : d215841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214172 q = 0) : d215833 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214172, d215833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
    | true =>
      simp only [d214172, d215833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20969 q selected
  have h2 (q : Pattern) (selected : d214173 q = 0) : d215834 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214173, d215834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214173, d215834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214174 q = 0) : d215835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214174, d215835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214174, d215835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214179 q = 0) : d215840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214179, d215840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214179, d215840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214180 q = 0) : d215841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214180, d215841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214180, d215841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20972 (p : Pattern) (selected : d214186 p = 0) : d215847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214177 q = 0) : d215838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20970 q selected
    | true =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214178 q = 0) : d215839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214183 q = 0) : d215844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214184 q = 0) : d215845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214184, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214184, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214185 q = 0) : d215846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214185, d215846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214185, d215846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214186 q = 0) : d215847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214186, d215847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214186, d215847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20973 (p : Pattern) (selected : d214190 p = 0) : d215851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214187 q = 0) : d215848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214188 q = 0) : d215849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214188, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214188, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214189 q = 0) : d215850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214189, d215850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214189, d215850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214190 q = 0) : d215851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214190, d215851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214190, d215851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20974 (p : Pattern) (selected : d214196 p = 0) : d215857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214191 q = 0) : d215852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214191, d215852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20972 q selected
    | true =>
      simp only [d214191, d215852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20973 q selected
  have h2 (q : Pattern) (selected : d214192 q = 0) : d215853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214192, d215853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214192, d215853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214193 q = 0) : d215854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214193, d215854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214193, d215854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214194 q = 0) : d215855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214194, d215855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214194, d215855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214195 q = 0) : d215856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214195, d215856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214195, d215856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214196 q = 0) : d215857 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214196, d215857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214196, d215857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20975 (p : Pattern) (selected : d214199 p = 0) : d215860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214177 q = 0) : d215838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20970 q selected
    | true =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214178 q = 0) : d215839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214183 q = 0) : d215844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214184 q = 0) : d215845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214184, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214184, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214185 q = 0) : d215846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214185, d215846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214185, d215846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214199 q = 0) : d215860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214199, d215860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214199, d215860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20976 (p : Pattern) (selected : d214200 p = 0) : d215861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214187 q = 0) : d215848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214188 q = 0) : d215849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214188, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214188, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214189 q = 0) : d215850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214189, d215850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214189, d215850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214200 q = 0) : d215861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214200, d215861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214200, d215861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro20977 (p : Pattern) (selected : d214206 p = 0) : d215867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214191 q = 0) : d215852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214191, d215852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20972 q selected
    | true =>
      simp only [d214191, d215852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20973 q selected
  have h2 (q : Pattern) (selected : d214192 q = 0) : d215853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214192, d215853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214192, d215853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214193 q = 0) : d215854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214193, d215854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214193, d215854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214194 q = 0) : d215855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214194, d215855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214194, d215855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214195 q = 0) : d215856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214195, d215856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214195, d215856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214201 q = 0) : d215862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214201, d215862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20975 q selected
    | true =>
      simp only [d214201, d215862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20976 q selected
  have h7 (q : Pattern) (selected : d214202 q = 0) : d215863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214202, d215863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214202, d215863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214203 q = 0) : d215864 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214203, d215864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214203, d215864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214204 q = 0) : d215865 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214204, d215865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214204, d215865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214205 q = 0) : d215866 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214205, d215866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214205, d215866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214206 q = 0) : d215867 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214206, d215867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214206, d215867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro20978 (p : Pattern) (selected : d214211 p = 0) : d215872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214177 q = 0) : d215838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20970 q selected
    | true =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214178 q = 0) : d215839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214183 q = 0) : d215844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214184 q = 0) : d215845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214184, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214184, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214210 q = 0) : d215871 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214210, d215871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214210, d215871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214211 q = 0) : d215872 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214211, d215872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214211, d215872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20979 (p : Pattern) (selected : d214213 p = 0) : d215874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214187 q = 0) : d215848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214188 q = 0) : d215849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214188, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214188, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214212 q = 0) : d215873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214212, d215873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214212, d215873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214213 q = 0) : d215874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214213, d215874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214213, d215874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20980 (p : Pattern) (selected : d214220 p = 0) : d215881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214177 q = 0) : d215838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20970 q selected
    | true =>
      simp only [d214177, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214178 q = 0) : d215839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214178, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214183 q = 0) : d215844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214183, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214218 q = 0) : d215879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214218, d215879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214218, d215879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214219 q = 0) : d215880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214219, d215880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214219, d215880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214220 q = 0) : d215881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214220, d215881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214220, d215881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20981 (p : Pattern) (selected : d214223 p = 0) : d215884 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214187 q = 0) : d215848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214187, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214221 q = 0) : d215882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214221, d215882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214221, d215882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214222 q = 0) : d215883 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214222, d215883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214222, d215883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214223 q = 0) : d215884 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214223, d215884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214223, d215884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20982 (p : Pattern) (selected : d214229 p = 0) : d215890 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2144 q = 0) : d53423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro576 q selected
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2145 q = 0) : d53424 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2146 q = 0) : d53425 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10343 q = 0) : d101664 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10345 q = 0) : d101666 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17225 q = 0) : d127927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214227 q = 0) : d215888 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214227, d215888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214227, d215888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d13675 q = 0) : d113865 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214228 q = 0) : d215889 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214228, d215889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214228, d215889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214229 q = 0) : d215890 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214229, d215890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214229, d215890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro20983 (p : Pattern) (selected : d214232 p = 0) : d215893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13675 q = 0) : d113865 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15548 q = 0) : d123547 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214157 q = 0) : d215818 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214157, d215818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214157, d215818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214160 q = 0) : d215821 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214160, d215821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214160, d215821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214232 q = 0) : d215893 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214232, d215893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214232, d215893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20984 (p : Pattern) (selected : d214237 p = 0) : d215898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214230 q = 0) : d215891 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214230, d215891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20982 q selected
    | true =>
      simp only [d214230, d215891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20966 q selected
  have h2 (q : Pattern) (selected : d214231 q = 0) : d215892 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214231, d215892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214231, d215892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214233 q = 0) : d215894 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214233, d215894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20966 q selected
    | true =>
      simp only [d214233, d215894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20983 q selected
  have h4 (q : Pattern) (selected : d214234 q = 0) : d215895 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214234, d215895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214234, d215895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214235 q = 0) : d215896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214235, d215896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214235, d215896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214162 q = 0) : d215823 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214162, d215823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20966 q selected
    | true =>
      simp only [d214162, d215823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
  have h7 (q : Pattern) (selected : d214163 q = 0) : d215824 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214163, d215824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214163, d215824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214167 q = 0) : d215828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214167, d215828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
    | true =>
      simp only [d214167, d215828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20968 q selected
  have h9 (q : Pattern) (selected : d214168 q = 0) : d215829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214168, d215829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214168, d215829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214169 q = 0) : d215830 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214169, d215830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214169, d215830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214236 q = 0) : d215897 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214236, d215897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214236, d215897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d214237 q = 0) : d215898 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214237, d215898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214237, d215898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro20985 (p : Pattern) (selected : d214242 p = 0) : d215903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214162 q = 0) : d215823 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214162, d215823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20966 q selected
    | true =>
      simp only [d214162, d215823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
  have h2 (q : Pattern) (selected : d214163 q = 0) : d215824 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214163, d215824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214163, d215824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214167 q = 0) : d215828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214167, d215828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
    | true =>
      simp only [d214167, d215828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20968 q selected
  have h4 (q : Pattern) (selected : d214168 q = 0) : d215829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214168, d215829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214168, d215829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214169 q = 0) : d215830 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214169, d215830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214169, d215830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214240 q = 0) : d215901 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214240, d215901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214240, d215901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214241 q = 0) : d215902 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214241, d215902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214241, d215902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214242 q = 0) : d215903 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214242, d215903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214242, d215903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro20986 (p : Pattern) (selected : d214248 p = 0) : d215909 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214238 q = 0) : d215899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214238, d215899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20984 q selected
    | true =>
      simp only [d214238, d215899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214239 q = 0) : d215900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214239, d215900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214239, d215900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214243 q = 0) : d215904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214243, d215904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20985 q selected
    | true =>
      simp only [d214243, d215904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214244 q = 0) : d215905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214244, d215905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214244, d215905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214245 q = 0) : d215906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214245, d215906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214245, d215906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214246 q = 0) : d215907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214246, d215907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214246, d215907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214247 q = 0) : d215908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214247, d215908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214247, d215908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214248 q = 0) : d215909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214248, d215909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214248, d215909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20987 (p : Pattern) (selected : d214252 p = 0) : d215913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214243 q = 0) : d215904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214243, d215904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20985 q selected
    | true =>
      simp only [d214243, d215904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214244 q = 0) : d215905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214244, d215905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214244, d215905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214181 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20971 q selected
    | true =>
      simp only [d214181, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214182 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214182, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214249 q = 0) : d215910 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214249, d215910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214249, d215910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214250 q = 0) : d215911 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214250, d215911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214250, d215911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214251 q = 0) : d215912 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214251, d215912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214251, d215912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214252 q = 0) : d215913 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214252, d215913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214252, d215913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20988 (p : Pattern) (selected : d214256 p = 0) : d215819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2201 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro587 q selected
    | true =>
      simp only [d2201, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2202 q = 0) : d53315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2202, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2202, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2203 q = 0) : d53316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2203, d53316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2203, d53316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10458 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
    | true =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10460 q = 0) : d101687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10460, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10460, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17256 q = 0) : d127855 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17256, d127855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17256, d127855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214254 q = 0) : d215817 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214254, d215817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214254, d215817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10468 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
    | true =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10470 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10470, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15649 q = 0) : d113865 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15649, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15649, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10484 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15654 q = 0) : d123547 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15654, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15654, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d214255 q = 0) : d215818 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214255, d215818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214255, d215818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d214256 q = 0) : d215819 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214256, d215819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214256, d215819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro20989 (p : Pattern) (selected : d214259 p = 0) : d215822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2219 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
    | true =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2220 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2221 q = 0) : d53334 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2221, d53334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2221, d53334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10493 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
    | true =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10495 q = 0) : d101714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10495, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10495, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17261 q = 0) : d127860 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17261, d127860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17261, d127860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214257 q = 0) : d215820 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214257, d215820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214257, d215820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10484 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15654 q = 0) : d123547 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15654, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15654, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214258 q = 0) : d215821 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214258, d215821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214258, d215821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d214259 q = 0) : d215822 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214259, d215822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214259, d215822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro20990 (p : Pattern) (selected : d214264 p = 0) : d215827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10508 q = 0) : d69331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6778 q selected
    | true =>
      simp only [d10508, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10510 q = 0) : d69332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10510, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13710 q = 0) : d69333 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13710, d69333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13710, d69333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214262 q = 0) : d215825 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214262, d215825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214262, d215825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10521 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10523 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15661 q = 0) : d123554 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15661, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15661, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214263 q = 0) : d215826 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214263, d215826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214263, d215826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214264 q = 0) : d215827 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214264, d215827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214264, d215827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20991 (p : Pattern) (selected : d214269 p = 0) : d215832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2231 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2232 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2233 q = 0) : d53346 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2233, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2233, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214268 q = 0) : d215831 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214268, d215831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214268, d215831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10521 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10523 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15661 q = 0) : d123554 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15661, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15661, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214263 q = 0) : d215826 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214263, d215826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214263, d215826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214269 q = 0) : d215832 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214269, d215832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214269, d215832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro20992 (p : Pattern) (selected : d214274 p = 0) : d215837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214260 q = 0) : d215823 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214260, d215823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20988 q selected
    | true =>
      simp only [d214260, d215823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20989 q selected
  have h2 (q : Pattern) (selected : d214261 q = 0) : d215824 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214261, d215824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214261, d215824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214265 q = 0) : d215828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214265, d215828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20989 q selected
    | true =>
      simp only [d214265, d215828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20990 q selected
  have h4 (q : Pattern) (selected : d214266 q = 0) : d215829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214266, d215829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214266, d215829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214267 q = 0) : d215830 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214267, d215830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214267, d215830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214270 q = 0) : d215833 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214270, d215833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20989 q selected
    | true =>
      simp only [d214270, d215833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20991 q selected
  have h7 (q : Pattern) (selected : d214271 q = 0) : d215834 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214271, d215834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214271, d215834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214272 q = 0) : d215835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214272, d215835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214272, d215835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214273 q = 0) : d215836 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214273, d215836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214273, d215836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214274 q = 0) : d215837 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214274, d215837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214274, d215837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20993 (p : Pattern) (selected : d214278 p = 0) : d215841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214270 q = 0) : d215833 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214270, d215833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20989 q selected
    | true =>
      simp only [d214270, d215833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20991 q selected
  have h2 (q : Pattern) (selected : d214271 q = 0) : d215834 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214271, d215834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214271, d215834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214272 q = 0) : d215835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214272, d215835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214272, d215835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214277 q = 0) : d215840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214277, d215840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214277, d215840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214278 q = 0) : d215841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214278, d215841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214278, d215841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20994 (p : Pattern) (selected : d214284 p = 0) : d215847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214275 q = 0) : d215838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214275, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20992 q selected
    | true =>
      simp only [d214275, d215838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214276 q = 0) : d215839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214276, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214276, d215839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214279 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214279, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20993 q selected
    | true =>
      simp only [d214279, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214280 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214280, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214280, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214281 q = 0) : d215844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214281, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214281, d215844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214282 q = 0) : d215845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214282, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214282, d215845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d214283 q = 0) : d215846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214283, d215846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214283, d215846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214284 q = 0) : d215847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214284, d215847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214284, d215847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro20995 (p : Pattern) (selected : d214288 p = 0) : d215851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214279 q = 0) : d215842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214279, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20993 q selected
    | true =>
      simp only [d214279, d215842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214280 q = 0) : d215843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214280, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214280, d215843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214285 q = 0) : d215848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214285, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214285, d215848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214286 q = 0) : d215849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214286, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214286, d215849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214287 q = 0) : d215850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214287, d215850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214287, d215850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214288 q = 0) : d215851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214288, d215851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214288, d215851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20996 (p : Pattern) (selected : d214291 p = 0) : d215916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2067 q = 0) : d53346 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d214170 q = 0) : d215831 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d214170, d215831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214170, d215831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214291 q = 0) : d215916 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d214291, d215916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214291, d215916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro20997 (p : Pattern) (selected : d214296 p = 0) : d215921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214162 q = 0) : d215823 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214162, d215823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20966 q selected
    | true =>
      simp only [d214162, d215823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
  have h2 (q : Pattern) (selected : d214163 q = 0) : d215824 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214163, d215824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214163, d215824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214167 q = 0) : d215828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214167, d215828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
    | true =>
      simp only [d214167, d215828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20968 q selected
  have h4 (q : Pattern) (selected : d214168 q = 0) : d215829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214168, d215829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214168, d215829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214169 q = 0) : d215830 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214169, d215830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214169, d215830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d214292 q = 0) : d215917 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d214292, d215917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20967 q selected
    | true =>
      simp only [d214292, d215917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20996 q selected
  have h7 (q : Pattern) (selected : d214293 q = 0) : d215918 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d214293, d215918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214293, d215918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d214294 q = 0) : d215919 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d214294, d215919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214294, d215919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d214295 q = 0) : d215920 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d214295, d215920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d214295, d215920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d214296 q = 0) : d215921 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d214296, d215921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d214296, d215921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro20998 (p : Pattern) (selected : d214302 p = 0) : d215927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214297 q = 0) : d215922 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d214297, d215922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20997 q selected
    | true =>
      simp only [d214297, d215922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d214298 q = 0) : d215923 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d214298, d215923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214298, d215923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214299 q = 0) : d215924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d214299, d215924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214299, d215924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214300 q = 0) : d215925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d214300, d215925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d214300, d215925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214301 q = 0) : d215926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d214301, d215926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214301, d215926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d214302 q = 0) : d215927 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d214302, d215927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214302, d215927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro20999 (p : Pattern) (selected : d214308 p = 0) : d215933 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d214214 q = 0) : d215875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214214, d215875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20978 q selected
    | true =>
      simp only [d214214, d215875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20979 q selected
  have h2 (q : Pattern) (selected : d214215 q = 0) : d215876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214215, d215876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214215, d215876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214216 q = 0) : d215877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214216, d215877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d214216, d215877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d214217 q = 0) : d215878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214217, d215878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214217, d215878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d214224 q = 0) : d215885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214224, d215885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20980 q selected
    | true =>
      simp only [d214224, d215885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20981 q selected
  have h6 (q : Pattern) (selected : d214225 q = 0) : d215886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214225, d215886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214225, d215886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d214226 q = 0) : d215887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214226, d215887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d214226, d215887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d214253 q = 0) : d215914 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214253, d215914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20986 q selected
    | true =>
      simp only [d214253, d215914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20987 q selected
  have h9 (q : Pattern) (selected : d214289 q = 0) : d215852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214289, d215852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20994 q selected
    | true =>
      simp only [d214289, d215852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20995 q selected
  have h10 (q : Pattern) (selected : d214290 q = 0) : d215915 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214290, d215915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d214290, d215915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d214303 q = 0) : d215928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d214303, d215928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20998 q selected
    | true =>
      simp only [d214303, d215928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d214304 q = 0) : d215929 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d214304, d215929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d214304, d215929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d214305 q = 0) : d215930 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d214305, d215930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d214305, d215930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d214306 q = 0) : d215931 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d214306, d215931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d214306, d215931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d214307 q = 0) : d215932 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d214307, d215932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d214307, d215932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d214308 q = 0) : d215933 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d214308, d215933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d214308, d215933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
end NetHack.Soko22Hazard87
