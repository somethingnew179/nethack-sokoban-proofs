import NetHack.Soko22Hazard87.EqIntroBlocks0055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro14000 (p : Pattern) (selected : d154326 p = 0) : d156072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154317 q = 0) : d156063 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154317, d156063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154317, d156063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13963 q selected
  have h2 (q : Pattern) (selected : d154142 q = 0) : d155959 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154142, d155959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13963 q selected
    | true =>
      simp only [d154142, d155959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154318 q = 0) : d156064 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154318, d156064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154318, d156064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154143 q = 0) : d155960 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154143, d155960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154143, d155960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154319 q = 0) : d156065 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154319, d156065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154319, d156065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154320 q = 0) : d156066 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154320, d156066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154320, d156066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154321 q = 0) : d156067 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154321, d156067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154321, d156067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13942 q selected
  have h8 (q : Pattern) (selected : d154039 q = 0) : d155856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154039, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13942 q selected
    | true =>
      simp only [d154039, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154322 q = 0) : d156068 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154322, d156068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154322, d156068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154040 q = 0) : d155857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154040, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154040, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154323 q = 0) : d156069 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154323, d156069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154323, d156069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154324 q = 0) : d156070 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154324, d156070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154324, d156070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154325 q = 0) : d156071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154325, d156071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154325, d156071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154326 q = 0) : d156072 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154326, d156072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154326, d156072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro14001 (p : Pattern) (selected : d154337 p = 0) : d156083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154321 q = 0) : d156067 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154321, d156067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154321, d156067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13942 q selected
  have h2 (q : Pattern) (selected : d154039 q = 0) : d155856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154039, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13942 q selected
    | true =>
      simp only [d154039, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154322 q = 0) : d156068 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154322, d156068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154322, d156068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154040 q = 0) : d155857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154040, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154040, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154323 q = 0) : d156069 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154323, d156069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154323, d156069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154324 q = 0) : d156070 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154324, d156070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154324, d156070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154327 q = 0) : d156073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154327, d156073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154327, d156073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13943 q selected
  have h8 (q : Pattern) (selected : d154045 q = 0) : d155862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154045, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13943 q selected
    | true =>
      simp only [d154045, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154328 q = 0) : d156074 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154328, d156074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154328, d156074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154046 q = 0) : d155863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154046, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154046, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154329 q = 0) : d156075 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154329, d156075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154329, d156075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154330 q = 0) : d156076 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154330, d156076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154330, d156076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154331 q = 0) : d156077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154331, d156077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154331, d156077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154332 q = 0) : d156078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154332, d156078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154332, d156078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13944 q selected
  have h15 (q : Pattern) (selected : d154052 q = 0) : d155869 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13944 q selected
    | true =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d154333 q = 0) : d156079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154333, d156079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d154333, d156079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154053 q = 0) : d155870 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d154334 q = 0) : d156080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154334, d156080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154334, d156080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d154335 q = 0) : d156081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154335, d156081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d154335, d156081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d154336 q = 0) : d156082 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154336, d156082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154336, d156082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d154337 q = 0) : d156083 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154337, d156083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154337, d156083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro14002 (p : Pattern) (selected : d154347 p = 0) : d156093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154341 q = 0) : d156087 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154341, d156087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154341, d156087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13965 q selected
  have h2 (q : Pattern) (selected : d154153 q = 0) : d155970 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154153, d155970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13965 q selected
    | true =>
      simp only [d154153, d155970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154342 q = 0) : d156088 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154342, d156088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154342, d156088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154154 q = 0) : d155971 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154154, d155971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154154, d155971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154343 q = 0) : d156089 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154343, d156089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154343, d156089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154344 q = 0) : d156090 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154344, d156090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154344, d156090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154332 q = 0) : d156078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154332, d156078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154332, d156078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13944 q selected
  have h8 (q : Pattern) (selected : d154052 q = 0) : d155869 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13944 q selected
    | true =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154333 q = 0) : d156079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154333, d156079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154333, d156079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154053 q = 0) : d155870 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154334 q = 0) : d156080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154334, d156080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154334, d156080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154335 q = 0) : d156081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154335, d156081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154335, d156081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154345 q = 0) : d156091 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154345, d156091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154345, d156091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154346 q = 0) : d156092 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154346, d156092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154346, d156092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d154347 q = 0) : d156093 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154347, d156093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154347, d156093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14003 (p : Pattern) (selected : d154357 p = 0) : d156103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154327 q = 0) : d156073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154327, d156073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154327, d156073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13943 q selected
  have h2 (q : Pattern) (selected : d154045 q = 0) : d155862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154045, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13943 q selected
    | true =>
      simp only [d154045, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154328 q = 0) : d156074 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154328, d156074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154328, d156074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154046 q = 0) : d155863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154046, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154046, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154329 q = 0) : d156075 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154329, d156075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154329, d156075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154330 q = 0) : d156076 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154330, d156076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154330, d156076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154352 q = 0) : d156098 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154352, d156098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154352, d156098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13946 q selected
  have h8 (q : Pattern) (selected : d154060 q = 0) : d155877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154060, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13946 q selected
    | true =>
      simp only [d154060, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154353 q = 0) : d156099 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154353, d156099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154353, d156099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154061 q = 0) : d155878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154061, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154061, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154354 q = 0) : d156100 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154354, d156100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154354, d156100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154355 q = 0) : d156101 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154355, d156101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154355, d156101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154356 q = 0) : d156102 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154356, d156102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154356, d156102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154332 q = 0) : d156078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154332, d156078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154332, d156078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13944 q selected
  have h15 (q : Pattern) (selected : d154052 q = 0) : d155869 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13944 q selected
    | true =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d154333 q = 0) : d156079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154333, d156079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d154333, d156079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154053 q = 0) : d155870 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d154334 q = 0) : d156080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154334, d156080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154334, d156080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d154335 q = 0) : d156081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154335, d156081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d154335, d156081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d154346 q = 0) : d156092 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154346, d156092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d154346, d156092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d154357 q = 0) : d156103 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154357, d156103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154357, d156103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro14004 (p : Pattern) (selected : d154366 p = 0) : d156112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154361 q = 0) : d156107 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154361, d156107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154361, d156107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13948 q selected
  have h2 (q : Pattern) (selected : d154072 q = 0) : d155889 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154072, d155889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13948 q selected
    | true =>
      simp only [d154072, d155889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154362 q = 0) : d156108 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154362, d156108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154362, d156108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154073 q = 0) : d155890 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154073, d155890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154073, d155890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154363 q = 0) : d156109 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154363, d156109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154363, d156109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154364 q = 0) : d156110 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154364, d156110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154364, d156110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154365 q = 0) : d156111 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154365, d156111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154365, d156111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154366 q = 0) : d156112 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154366, d156112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154366, d156112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14005 (p : Pattern) (selected : d154372 p = 0) : d156118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154338 q = 0) : d156084 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154338, d156084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14000 q selected
    | true =>
      simp only [d154338, d156084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14001 q selected
  have h2 (q : Pattern) (selected : d154339 q = 0) : d156085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154339, d156085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154339, d156085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154340 q = 0) : d156086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154340, d156086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154340, d156086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154348 q = 0) : d156094 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154348, d156094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14001 q selected
    | true =>
      simp only [d154348, d156094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14002 q selected
  have h5 (q : Pattern) (selected : d154349 q = 0) : d156095 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154349, d156095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154349, d156095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154350 q = 0) : d156096 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154350, d156096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154350, d156096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154351 q = 0) : d156097 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154351, d156097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154351, d156097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154358 q = 0) : d156104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154358, d156104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14001 q selected
    | true =>
      simp only [d154358, d156104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14003 q selected
  have h9 (q : Pattern) (selected : d154359 q = 0) : d156105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154359, d156105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154359, d156105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154360 q = 0) : d156106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154360, d156106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154360, d156106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154367 q = 0) : d156113 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154367, d156113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14003 q selected
    | true =>
      simp only [d154367, d156113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14004 q selected
  have h12 (q : Pattern) (selected : d154368 q = 0) : d156114 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154368, d156114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154368, d156114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154369 q = 0) : d156115 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154369, d156115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154369, d156115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154370 q = 0) : d156116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154370, d156116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154370, d156116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154371 q = 0) : d156117 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154371, d156117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154371, d156117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154372 q = 0) : d156118 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154372, d156118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154372, d156118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14006 (p : Pattern) (selected : d154377 p = 0) : d156123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154358 q = 0) : d156104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154358, d156104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14001 q selected
    | true =>
      simp only [d154358, d156104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14003 q selected
  have h2 (q : Pattern) (selected : d154359 q = 0) : d156105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154359, d156105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154359, d156105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154360 q = 0) : d156106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154360, d156106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154360, d156106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154367 q = 0) : d156113 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154367, d156113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14003 q selected
    | true =>
      simp only [d154367, d156113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14004 q selected
  have h5 (q : Pattern) (selected : d154368 q = 0) : d156114 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154368, d156114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154368, d156114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154369 q = 0) : d156115 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154369, d156115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154369, d156115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154370 q = 0) : d156116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154370, d156116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154370, d156116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154375 q = 0) : d156121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154375, d156121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154375, d156121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154376 q = 0) : d156122 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154376, d156122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154376, d156122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154377 q = 0) : d156123 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154377, d156123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154377, d156123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14007 (p : Pattern) (selected : d154383 p = 0) : d156129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154373 q = 0) : d156119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154373, d156119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14005 q selected
    | true =>
      simp only [d154373, d156119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154374 q = 0) : d156120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154374, d156120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154374, d156120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154378 q = 0) : d156124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154378, d156124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14006 q selected
    | true =>
      simp only [d154378, d156124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154379 q = 0) : d156125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154379, d156125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154379, d156125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154380 q = 0) : d156126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154380, d156126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154380, d156126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154381 q = 0) : d156127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154381, d156127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154381, d156127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154382 q = 0) : d156128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154382, d156128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154382, d156128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154383 q = 0) : d156129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154383, d156129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154383, d156129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14008 (p : Pattern) (selected : d154385 p = 0) : d156131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154352 q = 0) : d156098 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154352, d156098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154352, d156098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13946 q selected
  have h2 (q : Pattern) (selected : d154060 q = 0) : d155877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154060, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13946 q selected
    | true =>
      simp only [d154060, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154353 q = 0) : d156099 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154353, d156099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154353, d156099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154061 q = 0) : d155878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154061, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154061, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154354 q = 0) : d156100 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154354, d156100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154354, d156100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154355 q = 0) : d156101 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154355, d156101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154355, d156101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154384 q = 0) : d156130 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154384, d156130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154384, d156130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154385 q = 0) : d156131 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154385, d156131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154385, d156131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14009 (p : Pattern) (selected : d154391 p = 0) : d156137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154386 q = 0) : d156132 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154386, d156132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14003 q selected
    | true =>
      simp only [d154386, d156132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14008 q selected
  have h2 (q : Pattern) (selected : d154387 q = 0) : d156133 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154387, d156133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154387, d156133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154388 q = 0) : d156134 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154388, d156134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154388, d156134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154389 q = 0) : d156135 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154389, d156135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154389, d156135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154390 q = 0) : d156136 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154390, d156136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154390, d156136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154391 q = 0) : d156137 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154391, d156137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154391, d156137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14010 (p : Pattern) (selected : d154397 p = 0) : d156143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154378 q = 0) : d156124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154378, d156124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14006 q selected
    | true =>
      simp only [d154378, d156124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154379 q = 0) : d156125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154379, d156125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154379, d156125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154392 q = 0) : d156138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154392, d156138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14009 q selected
    | true =>
      simp only [d154392, d156138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154393 q = 0) : d156139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154393, d156139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154393, d156139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154394 q = 0) : d156140 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154394, d156140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154394, d156140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154395 q = 0) : d156141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154395, d156141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154395, d156141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154396 q = 0) : d156142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154396, d156142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154396, d156142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154397 q = 0) : d156143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154397, d156143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154397, d156143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14011 (p : Pattern) (selected : d154413 p = 0) : d156083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154399 q = 0) : d156067 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154399, d156067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154399, d156067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13971 q selected
  have h2 (q : Pattern) (selected : d154183 q = 0) : d155856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154183, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13971 q selected
    | true =>
      simp only [d154183, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154400 q = 0) : d156068 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154400, d156068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154400, d156068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154184 q = 0) : d155857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154184, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154184, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154401 q = 0) : d156069 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154401, d156069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154401, d156069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154402 q = 0) : d156070 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154402, d156070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154402, d156070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154403 q = 0) : d156073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154403, d156073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154403, d156073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13972 q selected
  have h8 (q : Pattern) (selected : d154189 q = 0) : d155862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154189, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13972 q selected
    | true =>
      simp only [d154189, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154404 q = 0) : d156074 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154404, d156074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154404, d156074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154190 q = 0) : d155863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154190, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154190, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154405 q = 0) : d156075 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154405, d156075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154405, d156075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154406 q = 0) : d156076 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154406, d156076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154406, d156076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154407 q = 0) : d156077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154407, d156077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154407, d156077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154408 q = 0) : d156078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154408, d156078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154408, d156078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13973 q selected
  have h15 (q : Pattern) (selected : d154196 q = 0) : d155869 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154196, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13973 q selected
    | true =>
      simp only [d154196, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d154409 q = 0) : d156079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154409, d156079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d154409, d156079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154197 q = 0) : d155870 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154197, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154197, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d154410 q = 0) : d156080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154410, d156080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154410, d156080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d154411 q = 0) : d156081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154411, d156081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d154411, d156081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d154412 q = 0) : d156082 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154412, d156082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154412, d156082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d154413 q = 0) : d156083 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154413, d156083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154413, d156083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro14012 (p : Pattern) (selected : d154420 p = 0) : d156103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154403 q = 0) : d156073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154403, d156073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154403, d156073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13972 q selected
  have h2 (q : Pattern) (selected : d154189 q = 0) : d155862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154189, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13972 q selected
    | true =>
      simp only [d154189, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154404 q = 0) : d156074 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154404, d156074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154404, d156074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154190 q = 0) : d155863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154190, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154190, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154405 q = 0) : d156075 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154405, d156075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154405, d156075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154406 q = 0) : d156076 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154406, d156076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154406, d156076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154414 q = 0) : d156098 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154414, d156098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154414, d156098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13975 q selected
  have h8 (q : Pattern) (selected : d154204 q = 0) : d155877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154204, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13975 q selected
    | true =>
      simp only [d154204, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154415 q = 0) : d156099 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154415, d156099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154415, d156099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154205 q = 0) : d155878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154205, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154205, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154416 q = 0) : d156100 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154416, d156100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154416, d156100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154417 q = 0) : d156101 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154417, d156101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154417, d156101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154418 q = 0) : d156102 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154418, d156102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154418, d156102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154408 q = 0) : d156078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154408, d156078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154408, d156078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13973 q selected
  have h15 (q : Pattern) (selected : d154196 q = 0) : d155869 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154196, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13973 q selected
    | true =>
      simp only [d154196, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d154409 q = 0) : d156079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154409, d156079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d154409, d156079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154197 q = 0) : d155870 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154197, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154197, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d154410 q = 0) : d156080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154410, d156080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154410, d156080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d154411 q = 0) : d156081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154411, d156081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d154411, d156081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d154419 q = 0) : d156092 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154419, d156092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d154419, d156092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d154420 q = 0) : d156103 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154420, d156103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154420, d156103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro14013 (p : Pattern) (selected : d154429 p = 0) : d156112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154424 q = 0) : d156107 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154424, d156107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154424, d156107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13977 q selected
  have h2 (q : Pattern) (selected : d154216 q = 0) : d155889 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154216, d155889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13977 q selected
    | true =>
      simp only [d154216, d155889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154425 q = 0) : d156108 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154425, d156108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154425, d156108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154217 q = 0) : d155890 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154217, d155890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154217, d155890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154426 q = 0) : d156109 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154426, d156109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154426, d156109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154427 q = 0) : d156110 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154427, d156110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154427, d156110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154428 q = 0) : d156111 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154428, d156111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154428, d156111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154429 q = 0) : d156112 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154429, d156112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154429, d156112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14014 (p : Pattern) (selected : d154435 p = 0) : d156131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154414 q = 0) : d156098 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154414, d156098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154414, d156098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13975 q selected
  have h2 (q : Pattern) (selected : d154204 q = 0) : d155877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154204, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13975 q selected
    | true =>
      simp only [d154204, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154415 q = 0) : d156099 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154415, d156099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154415, d156099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154205 q = 0) : d155878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154205, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154205, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154416 q = 0) : d156100 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154416, d156100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154416, d156100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154417 q = 0) : d156101 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154417, d156101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154417, d156101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154434 q = 0) : d156130 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154434, d156130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154434, d156130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154435 q = 0) : d156131 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154435, d156131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154435, d156131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14015 (p : Pattern) (selected : d154441 p = 0) : d156146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154421 q = 0) : d156104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154421, d156104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14011 q selected
    | true =>
      simp only [d154421, d156104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14012 q selected
  have h2 (q : Pattern) (selected : d154422 q = 0) : d156105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154422, d156105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154422, d156105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154423 q = 0) : d156106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154423, d156106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154423, d156106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154430 q = 0) : d156113 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154430, d156113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14012 q selected
    | true =>
      simp only [d154430, d156113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14013 q selected
  have h5 (q : Pattern) (selected : d154431 q = 0) : d156114 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154431, d156114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154431, d156114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154432 q = 0) : d156115 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154432, d156115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154432, d156115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154433 q = 0) : d156116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154433, d156116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154433, d156116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154436 q = 0) : d156132 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154436, d156132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14012 q selected
    | true =>
      simp only [d154436, d156132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14014 q selected
  have h9 (q : Pattern) (selected : d154437 q = 0) : d156133 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154437, d156133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154437, d156133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154438 q = 0) : d156134 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154438, d156134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154438, d156134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154439 q = 0) : d156135 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154439, d156135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154439, d156135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154440 q = 0) : d156145 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154440, d156145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154440, d156145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154441 q = 0) : d156146 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154441, d156146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154441, d156146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14016 (p : Pattern) (selected : d154445 p = 0) : d156137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154436 q = 0) : d156132 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154436, d156132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14012 q selected
    | true =>
      simp only [d154436, d156132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14014 q selected
  have h2 (q : Pattern) (selected : d154437 q = 0) : d156133 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154437, d156133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154437, d156133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154438 q = 0) : d156134 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154438, d156134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154438, d156134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154439 q = 0) : d156135 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154439, d156135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154439, d156135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154444 q = 0) : d156136 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154444, d156136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154444, d156136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154445 q = 0) : d156137 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154445, d156137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154445, d156137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14017 (p : Pattern) (selected : d154451 p = 0) : d156152 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154442 q = 0) : d156147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154442, d156147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14015 q selected
    | true =>
      simp only [d154442, d156147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154443 q = 0) : d156148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154443, d156148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154443, d156148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154446 q = 0) : d156138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154446, d156138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14016 q selected
    | true =>
      simp only [d154446, d156138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154447 q = 0) : d156139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154447, d156139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154447, d156139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154448 q = 0) : d156149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154448, d156149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154448, d156149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154449 q = 0) : d156150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154449, d156150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154449, d156150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154450 q = 0) : d156151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154450, d156151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154450, d156151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154451 q = 0) : d156152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154451, d156152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154451, d156152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14018 (p : Pattern) (selected : d154455 p = 0) : d156156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154446 q = 0) : d156138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154446, d156138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14016 q selected
    | true =>
      simp only [d154446, d156138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154447 q = 0) : d156139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154447, d156139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154447, d156139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154452 q = 0) : d156153 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154452, d156153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154452, d156153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154453 q = 0) : d156154 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154453, d156154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154453, d156154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154454 q = 0) : d156155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154454, d156155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154454, d156155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154455 q = 0) : d156156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154455, d156156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154455, d156156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14019 (p : Pattern) (selected : d154459 p = 0) : d156146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154358 q = 0) : d156104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154358, d156104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14001 q selected
    | true =>
      simp only [d154358, d156104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14003 q selected
  have h2 (q : Pattern) (selected : d154359 q = 0) : d156105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154359, d156105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154359, d156105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154360 q = 0) : d156106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154360, d156106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154360, d156106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154367 q = 0) : d156113 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154367, d156113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14003 q selected
    | true =>
      simp only [d154367, d156113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14004 q selected
  have h5 (q : Pattern) (selected : d154368 q = 0) : d156114 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154368, d156114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154368, d156114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154369 q = 0) : d156115 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154369, d156115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154369, d156115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154370 q = 0) : d156116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154370, d156116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154370, d156116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154386 q = 0) : d156132 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154386, d156132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14003 q selected
    | true =>
      simp only [d154386, d156132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14008 q selected
  have h9 (q : Pattern) (selected : d154387 q = 0) : d156133 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154387, d156133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154387, d156133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154388 q = 0) : d156134 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154388, d156134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154388, d156134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154389 q = 0) : d156135 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154389, d156135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154389, d156135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154458 q = 0) : d156145 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154458, d156145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154458, d156145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154459 q = 0) : d156146 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154459, d156146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154459, d156146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14020 (p : Pattern) (selected : d154465 p = 0) : d156162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154460 q = 0) : d156147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154460, d156147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14019 q selected
    | true =>
      simp only [d154460, d156147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154461 q = 0) : d156148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154461, d156148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154461, d156148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154462 q = 0) : d156159 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154462, d156159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154462, d156159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154463 q = 0) : d156160 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154463, d156160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154463, d156160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154464 q = 0) : d156161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154464, d156161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154464, d156161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154465 q = 0) : d156162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154465, d156162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154465, d156162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14021 (p : Pattern) (selected : d154471 p = 0) : d156168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154398 q = 0) : d156144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154398, d156144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14007 q selected
    | true =>
      simp only [d154398, d156144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14010 q selected
  have h2 (q : Pattern) (selected : d154456 q = 0) : d156157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154456, d156157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14017 q selected
    | true =>
      simp only [d154456, d156157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14018 q selected
  have h3 (q : Pattern) (selected : d154457 q = 0) : d156158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154457, d156158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154457, d156158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154466 q = 0) : d156163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154466, d156163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14020 q selected
    | true =>
      simp only [d154466, d156163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154467 q = 0) : d156164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154467, d156164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154467, d156164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154468 q = 0) : d156165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154468, d156165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154468, d156165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154469 q = 0) : d156166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154469, d156166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154469, d156166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154470 q = 0) : d156167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154470, d156167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154470, d156167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154471 q = 0) : d156168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154471, d156168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154471, d156168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14022 (p : Pattern) (selected : d154476 p = 0) : d156156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154392 q = 0) : d156138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154392, d156138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14009 q selected
    | true =>
      simp only [d154392, d156138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154393 q = 0) : d156139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154393, d156139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154393, d156139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154473 q = 0) : d156153 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154473, d156153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154473, d156153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154474 q = 0) : d156154 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154474, d156154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154474, d156154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154475 q = 0) : d156155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154475, d156155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154475, d156155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154476 q = 0) : d156156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154476, d156156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154476, d156156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14023 (p : Pattern) (selected : d154482 p = 0) : d156175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154477 q = 0) : d156170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154477, d156170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14022 q selected
    | true =>
      simp only [d154477, d156170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154478 q = 0) : d156171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154478, d156171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154478, d156171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154479 q = 0) : d156172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154479, d156172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154479, d156172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154480 q = 0) : d156173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154480, d156173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154480, d156173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154481 q = 0) : d156174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154481, d156174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154481, d156174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154482 q = 0) : d156175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154482, d156175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154482, d156175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14024 (p : Pattern) (selected : d154488 p = 0) : d156181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154110 q = 0) : d155927 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154110, d155927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154110, d155927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13955 q selected
  have h2 (q : Pattern) (selected : d154111 q = 0) : d155928 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154111, d155928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154111, d155928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154120 q = 0) : d155937 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154120, d155937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13955 q selected
    | true =>
      simp only [d154120, d155937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13958 q selected
  have h4 (q : Pattern) (selected : d154121 q = 0) : d155938 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154121, d155938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154121, d155938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154122 q = 0) : d155939 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154122, d155939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154122, d155939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154285 q = 0) : d156031 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154285, d156031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13985 q selected
    | true =>
      simp only [d154285, d156031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13995 q selected
  have h7 (q : Pattern) (selected : d154303 q = 0) : d156049 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154303, d156049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13996 q selected
    | true =>
      simp only [d154303, d156049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13997 q selected
  have h8 (q : Pattern) (selected : d154304 q = 0) : d156050 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154304, d156050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154304, d156050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154305 q = 0) : d156051 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154305, d156051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154305, d156051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d154306 q = 0) : d156052 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154306, d156052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154306, d156052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154310 q = 0) : d156056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154310, d156056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154310, d156056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13998 q selected
  have h12 (q : Pattern) (selected : d154312 q = 0) : d156058 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154312, d156058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154312, d156058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13999 q selected
  have h13 (q : Pattern) (selected : d154313 q = 0) : d156059 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154313, d156059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154313, d156059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154314 q = 0) : d156060 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154314, d156060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154314, d156060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d154315 q = 0) : d156061 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154315, d156061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d154315, d156061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d154316 q = 0) : d156062 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154316, d156062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154316, d156062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154472 q = 0) : d156169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154472, d156169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154472, d156169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14021 q selected
  have h18 (q : Pattern) (selected : d154483 q = 0) : d156176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154483, d156176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154483, d156176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14023 q selected
  have h19 (q : Pattern) (selected : d154484 q = 0) : d156177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154484, d156177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d154484, d156177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d154485 q = 0) : d156178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154485, d156178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d154485, d156178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d154486 q = 0) : d156179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154486, d156179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d154486, d156179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d154487 q = 0) : d156180 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154487, d156180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d154487, d156180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d154488 q = 0) : d156181 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d154488, d156181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154488, d156181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro14025 (p : Pattern) (selected : d154494 p = 0) : d156187 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154489 q = 0) : d156182 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d154489, d156182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154489, d156182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14024 q selected
  have h2 (q : Pattern) (selected : d154490 q = 0) : d156183 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d154490, d156183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154490, d156183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154491 q = 0) : d156184 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d154491, d156184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154491, d156184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154492 q = 0) : d156185 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d154492, d156185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154492, d156185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154493 q = 0) : d156186 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d154493, d156186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154493, d156186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154494 q = 0) : d156187 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d154494, d156187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154494, d156187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14026 (p : Pattern) (selected : d154500 p = 0) : d156193 p = 1 := by
  have h0 (q : Pattern) (selected : d2004 q = 0) : d53283 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro546 q selected
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro547 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2008 q = 0) : d53287 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro548 q selected
  have h3 (q : Pattern) (selected : d2009 q = 0) : d53288 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154499 q = 0) : d156192 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154499, d156192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154499, d156192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d154500 q = 0) : d156193 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154500, d156193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154500, d156193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro14027 (p : Pattern) (selected : d154506 p = 0) : d156199 p = 1 := by
  have h0 (q : Pattern) (selected : d2020 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro549 q selected
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro550 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2024 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro551 q selected
  have h3 (q : Pattern) (selected : d2025 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2029 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro552 q selected
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2030 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154505 q = 0) : d156198 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154505, d156198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154505, d156198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154506 q = 0) : d156199 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154506, d156199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154506, d156199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro14028 (p : Pattern) (selected : d154512 p = 0) : d156205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154501 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
    | true =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154502 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154503 q = 0) : d156196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154503, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154503, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154504 q = 0) : d156197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154504, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154504, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154507 q = 0) : d156200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154507, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14027 q selected
    | true =>
      simp only [d154507, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154508 q = 0) : d156201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154508, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154508, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154509 q = 0) : d156202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154509, d156202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154509, d156202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154510 q = 0) : d156203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154510, d156203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154510, d156203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154511 q = 0) : d156204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154511, d156204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154511, d156204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154512 q = 0) : d156205 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154512, d156205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154512, d156205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14029 (p : Pattern) (selected : d154514 p = 0) : d156207 p = 1 := by
  have h0 (q : Pattern) (selected : d2041 q = 0) : d53320 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro554 q selected
    | true =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2043 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
  have h3 (q : Pattern) (selected : d2044 q = 0) : d53323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2047 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2048 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154513 q = 0) : d156206 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154513, d156206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154513, d156206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154514 q = 0) : d156207 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154514, d156207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154514, d156207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro14030 (p : Pattern) (selected : d154520 p = 0) : d156213 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154507 q = 0) : d156200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154507, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14027 q selected
    | true =>
      simp only [d154507, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154508 q = 0) : d156201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154508, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154508, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154509 q = 0) : d156202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154509, d156202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154509, d156202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154510 q = 0) : d156203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154510, d156203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154510, d156203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154515 q = 0) : d156208 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154515, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14029 q selected
    | true =>
      simp only [d154515, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154516 q = 0) : d156209 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154516, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154516, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154517 q = 0) : d156210 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154517, d156210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154517, d156210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154518 q = 0) : d156211 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154518, d156211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154518, d156211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154519 q = 0) : d156212 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154519, d156212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154519, d156212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154520 q = 0) : d156213 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154520, d156213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154520, d156213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14031 (p : Pattern) (selected : d154525 p = 0) : d156218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5238 q = 0) : d69322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
  have h2 (q : Pattern) (selected : d5239 q = 0) : d69323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2047 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2048 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154524 q = 0) : d156217 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154524, d156217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154524, d156217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154525 q = 0) : d156218 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154525, d156218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154525, d156218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14032 (p : Pattern) (selected : d154531 p = 0) : d156224 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154526 q = 0) : d156219 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154526, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14031 q selected
    | true =>
      simp only [d154526, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154527 q = 0) : d156220 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154527, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154527, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154528 q = 0) : d156221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154528, d156221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154528, d156221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154529 q = 0) : d156222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154529, d156222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154529, d156222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154530 q = 0) : d156223 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154530, d156223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154530, d156223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154531 q = 0) : d156224 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154531, d156224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154531, d156224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14033 (p : Pattern) (selected : d154537 p = 0) : d156230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154515 q = 0) : d156208 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154515, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14029 q selected
    | true =>
      simp only [d154515, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154516 q = 0) : d156209 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154516, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154516, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154517 q = 0) : d156210 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154517, d156210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154517, d156210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154518 q = 0) : d156211 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154518, d156211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154518, d156211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154536 q = 0) : d156229 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154536, d156229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154536, d156229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154537 q = 0) : d156230 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154537, d156230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154537, d156230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14034 (p : Pattern) (selected : d154543 p = 0) : d156236 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154521 q = 0) : d156214 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154521, d156214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14028 q selected
    | true =>
      simp only [d154521, d156214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14030 q selected
  have h2 (q : Pattern) (selected : d154522 q = 0) : d156215 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154522, d156215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154522, d156215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154523 q = 0) : d156216 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154523, d156216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154523, d156216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154532 q = 0) : d156225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154532, d156225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14030 q selected
    | true =>
      simp only [d154532, d156225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14032 q selected
  have h5 (q : Pattern) (selected : d154533 q = 0) : d156226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154533, d156226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154533, d156226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154534 q = 0) : d156227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154534, d156227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154534, d156227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154535 q = 0) : d156228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154535, d156228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154535, d156228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154538 q = 0) : d156231 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154538, d156231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14030 q selected
    | true =>
      simp only [d154538, d156231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14033 q selected
  have h9 (q : Pattern) (selected : d154539 q = 0) : d156232 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154539, d156232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154539, d156232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154540 q = 0) : d156233 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154540, d156233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154540, d156233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154541 q = 0) : d156234 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154541, d156234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154541, d156234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154542 q = 0) : d156235 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154542, d156235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154542, d156235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154543 q = 0) : d156236 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154543, d156236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154543, d156236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14035 (p : Pattern) (selected : d154547 p = 0) : d156240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154538 q = 0) : d156231 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154538, d156231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14030 q selected
    | true =>
      simp only [d154538, d156231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14033 q selected
  have h2 (q : Pattern) (selected : d154539 q = 0) : d156232 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154539, d156232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154539, d156232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154540 q = 0) : d156233 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154540, d156233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154540, d156233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154541 q = 0) : d156234 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154541, d156234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154541, d156234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154546 q = 0) : d156239 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154546, d156239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154546, d156239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154547 q = 0) : d156240 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154547, d156240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154547, d156240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14036 (p : Pattern) (selected : d154553 p = 0) : d156246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154544 q = 0) : d156237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14034 q selected
    | true =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154545 q = 0) : d156238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154550 q = 0) : d156243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154551 q = 0) : d156244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154551, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154551, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154552 q = 0) : d156245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154552, d156245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154552, d156245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154553 q = 0) : d156246 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154553, d156246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154553, d156246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14037 (p : Pattern) (selected : d154557 p = 0) : d156250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154554 q = 0) : d156247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154555 q = 0) : d156248 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154555, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154555, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154556 q = 0) : d156249 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154556, d156249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154556, d156249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154557 q = 0) : d156250 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154557, d156250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154557, d156250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14038 (p : Pattern) (selected : d154563 p = 0) : d156256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154558 q = 0) : d156251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154558, d156251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14036 q selected
    | true =>
      simp only [d154558, d156251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14037 q selected
  have h2 (q : Pattern) (selected : d154559 q = 0) : d156252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154559, d156252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154559, d156252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154560 q = 0) : d156253 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154560, d156253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154560, d156253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154561 q = 0) : d156254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154561, d156254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154561, d156254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154562 q = 0) : d156255 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154562, d156255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154562, d156255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154563 q = 0) : d156256 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154563, d156256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154563, d156256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14039 (p : Pattern) (selected : d154566 p = 0) : d156259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154544 q = 0) : d156237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14034 q selected
    | true =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154545 q = 0) : d156238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154550 q = 0) : d156243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154551 q = 0) : d156244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154551, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154551, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154552 q = 0) : d156245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154552, d156245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154552, d156245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154566 q = 0) : d156259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154566, d156259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154566, d156259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14040 (p : Pattern) (selected : d154567 p = 0) : d156260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154554 q = 0) : d156247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154555 q = 0) : d156248 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154555, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154555, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154556 q = 0) : d156249 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154556, d156249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154556, d156249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154567 q = 0) : d156260 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154567, d156260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154567, d156260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14041 (p : Pattern) (selected : d154573 p = 0) : d156266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154558 q = 0) : d156251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154558, d156251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14036 q selected
    | true =>
      simp only [d154558, d156251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14037 q selected
  have h2 (q : Pattern) (selected : d154559 q = 0) : d156252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154559, d156252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154559, d156252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154560 q = 0) : d156253 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154560, d156253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154560, d156253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154561 q = 0) : d156254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154561, d156254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154561, d156254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154562 q = 0) : d156255 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154562, d156255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154562, d156255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154568 q = 0) : d156261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154568, d156261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14039 q selected
    | true =>
      simp only [d154568, d156261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14040 q selected
  have h7 (q : Pattern) (selected : d154569 q = 0) : d156262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154569, d156262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154569, d156262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154570 q = 0) : d156263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154570, d156263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154570, d156263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154571 q = 0) : d156264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154571, d156264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154571, d156264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154572 q = 0) : d156265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154572, d156265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154572, d156265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154573 q = 0) : d156266 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154573, d156266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154573, d156266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14042 (p : Pattern) (selected : d154578 p = 0) : d156271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154544 q = 0) : d156237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14034 q selected
    | true =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154545 q = 0) : d156238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154550 q = 0) : d156243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154551 q = 0) : d156244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154551, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154551, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154577 q = 0) : d156270 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154577, d156270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154577, d156270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154578 q = 0) : d156271 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154578, d156271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154578, d156271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14043 (p : Pattern) (selected : d154580 p = 0) : d156273 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154554 q = 0) : d156247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154555 q = 0) : d156248 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154555, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154555, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154579 q = 0) : d156272 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154579, d156272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154579, d156272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154580 q = 0) : d156273 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154580, d156273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154580, d156273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14044 (p : Pattern) (selected : d154587 p = 0) : d156280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154544 q = 0) : d156237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14034 q selected
    | true =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154545 q = 0) : d156238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154550 q = 0) : d156243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154585 q = 0) : d156278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154585, d156278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154585, d156278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154586 q = 0) : d156279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154586, d156279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154586, d156279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154587 q = 0) : d156280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154587, d156280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154587, d156280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14045 (p : Pattern) (selected : d154590 p = 0) : d156283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154554 q = 0) : d156247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154588 q = 0) : d156281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154588, d156281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154588, d156281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154589 q = 0) : d156282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154589, d156282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154589, d156282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154590 q = 0) : d156283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154590, d156283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154590, d156283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14046 (p : Pattern) (selected : d154595 p = 0) : d156288 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154501 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
    | true =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154502 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154503 q = 0) : d156196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154503, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154503, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154504 q = 0) : d156197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154504, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154504, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154594 q = 0) : d156287 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154594, d156287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154594, d156287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154595 q = 0) : d156288 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154595, d156288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154595, d156288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14047 (p : Pattern) (selected : d154604 p = 0) : d156297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154596 q = 0) : d156289 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154596, d156289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14046 q selected
    | true =>
      simp only [d154596, d156289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14028 q selected
  have h2 (q : Pattern) (selected : d154597 q = 0) : d156290 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154597, d156290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154597, d156290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154598 q = 0) : d156291 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154598, d156291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154598, d156291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154599 q = 0) : d156292 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154599, d156292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14028 q selected
    | true =>
      simp only [d154599, d156292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154600 q = 0) : d156293 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154600, d156293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154600, d156293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154601 q = 0) : d156294 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154601, d156294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154601, d156294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154602 q = 0) : d156295 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154602, d156295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154602, d156295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154521 q = 0) : d156214 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154521, d156214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14028 q selected
    | true =>
      simp only [d154521, d156214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14030 q selected
  have h9 (q : Pattern) (selected : d154522 q = 0) : d156215 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154522, d156215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154522, d156215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154523 q = 0) : d156216 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154523, d156216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154523, d156216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154532 q = 0) : d156225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154532, d156225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14030 q selected
    | true =>
      simp only [d154532, d156225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14032 q selected
  have h12 (q : Pattern) (selected : d154533 q = 0) : d156226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154533, d156226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154533, d156226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154534 q = 0) : d156227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154534, d156227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154534, d156227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154535 q = 0) : d156228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154535, d156228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154535, d156228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154603 q = 0) : d156296 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154603, d156296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154603, d156296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154604 q = 0) : d156297 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154604, d156297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154604, d156297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14048 (p : Pattern) (selected : d154609 p = 0) : d156302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154521 q = 0) : d156214 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154521, d156214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14028 q selected
    | true =>
      simp only [d154521, d156214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14030 q selected
  have h2 (q : Pattern) (selected : d154522 q = 0) : d156215 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154522, d156215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154522, d156215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154523 q = 0) : d156216 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154523, d156216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154523, d156216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154532 q = 0) : d156225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154532, d156225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14030 q selected
    | true =>
      simp only [d154532, d156225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14032 q selected
  have h5 (q : Pattern) (selected : d154533 q = 0) : d156226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154533, d156226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154533, d156226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154534 q = 0) : d156227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154534, d156227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154534, d156227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154535 q = 0) : d156228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154535, d156228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154535, d156228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154607 q = 0) : d156300 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154607, d156300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154607, d156300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154608 q = 0) : d156301 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154608, d156301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154608, d156301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154609 q = 0) : d156302 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154609, d156302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154609, d156302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14049 (p : Pattern) (selected : d154615 p = 0) : d156308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154605 q = 0) : d156298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154605, d156298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14047 q selected
    | true =>
      simp only [d154605, d156298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154606 q = 0) : d156299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154606, d156299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154606, d156299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154610 q = 0) : d156303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154610, d156303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14048 q selected
    | true =>
      simp only [d154610, d156303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154611 q = 0) : d156304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154611, d156304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154611, d156304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154612 q = 0) : d156305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154612, d156305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154612, d156305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154613 q = 0) : d156306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154613, d156306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154613, d156306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154614 q = 0) : d156307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154614, d156307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154614, d156307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154615 q = 0) : d156308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154615, d156308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154615, d156308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14050 (p : Pattern) (selected : d154619 p = 0) : d156312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154610 q = 0) : d156303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154610, d156303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14048 q selected
    | true =>
      simp only [d154610, d156303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154611 q = 0) : d156304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154611, d156304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154611, d156304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154616 q = 0) : d156309 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154616, d156309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154616, d156309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154617 q = 0) : d156310 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154617, d156310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154617, d156310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154618 q = 0) : d156311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154618, d156311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154618, d156311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154619 q = 0) : d156312 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154619, d156312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154619, d156312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14051 (p : Pattern) (selected : d154622 p = 0) : d156193 p = 1 := by
  have h0 (q : Pattern) (selected : d2170 q = 0) : d53283 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2170, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro580 q selected
    | true =>
      simp only [d2170, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro581 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2174 q = 0) : d53287 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2174, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro582 q selected
  have h3 (q : Pattern) (selected : d2175 q = 0) : d53288 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2175, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2175, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154621 q = 0) : d156192 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154621, d156192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154621, d156192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d154622 q = 0) : d156193 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154622, d156193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154622, d156193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro14052 (p : Pattern) (selected : d154628 p = 0) : d156199 p = 1 := by
  have h0 (q : Pattern) (selected : d2186 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro583 q selected
    | true =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro584 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2190 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro585 q selected
  have h3 (q : Pattern) (selected : d2191 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2195 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro586 q selected
    | true =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2196 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154627 q = 0) : d156198 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154627, d156198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154627, d156198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154628 q = 0) : d156199 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154628, d156199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154628, d156199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro14053 (p : Pattern) (selected : d154634 p = 0) : d156205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154623 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154623, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14051 q selected
    | true =>
      simp only [d154623, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154624 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154624, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154624, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154625 q = 0) : d156196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154625, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154625, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154626 q = 0) : d156197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154626, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154626, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154629 q = 0) : d156200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154629, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14052 q selected
    | true =>
      simp only [d154629, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154630 q = 0) : d156201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154630, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154630, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154631 q = 0) : d156202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154631, d156202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154631, d156202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154632 q = 0) : d156203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154632, d156203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154632, d156203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154633 q = 0) : d156204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154633, d156204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154633, d156204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154634 q = 0) : d156205 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154634, d156205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154634, d156205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14054 (p : Pattern) (selected : d154636 p = 0) : d156207 p = 1 := by
  have h0 (q : Pattern) (selected : d2207 q = 0) : d53320 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2207, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro588 q selected
    | true =>
      simp only [d2207, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2209 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
  have h3 (q : Pattern) (selected : d2210 q = 0) : d53323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2210, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2210, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2213 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
    | true =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2214 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154635 q = 0) : d156206 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154635, d156206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154635, d156206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154636 q = 0) : d156207 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154636, d156207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154636, d156207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro14055 (p : Pattern) (selected : d154642 p = 0) : d156213 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154629 q = 0) : d156200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154629, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14052 q selected
    | true =>
      simp only [d154629, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154630 q = 0) : d156201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154630, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154630, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154631 q = 0) : d156202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154631, d156202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154631, d156202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154632 q = 0) : d156203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154632, d156203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154632, d156203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154637 q = 0) : d156208 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154637, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14054 q selected
    | true =>
      simp only [d154637, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154638 q = 0) : d156209 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154638, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154638, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154639 q = 0) : d156210 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154639, d156210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154639, d156210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154640 q = 0) : d156211 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154640, d156211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154640, d156211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154641 q = 0) : d156212 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154641, d156212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154641, d156212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154642 q = 0) : d156213 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154642, d156213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154642, d156213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14056 (p : Pattern) (selected : d154647 p = 0) : d156218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10476 q = 0) : d69322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10476, d69322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10476, d69322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
  have h2 (q : Pattern) (selected : d10477 q = 0) : d69323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10477, d69323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10477, d69323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2213 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
    | true =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2214 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154646 q = 0) : d156217 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154646, d156217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154646, d156217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154647 q = 0) : d156218 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154647, d156218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154647, d156218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14057 (p : Pattern) (selected : d154653 p = 0) : d156224 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154648 q = 0) : d156219 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154648, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14056 q selected
    | true =>
      simp only [d154648, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154649 q = 0) : d156220 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154649, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154649, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154650 q = 0) : d156221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154650, d156221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154650, d156221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154651 q = 0) : d156222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154651, d156222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154651, d156222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154652 q = 0) : d156223 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154652, d156223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154652, d156223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154653 q = 0) : d156224 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154653, d156224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154653, d156224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14058 (p : Pattern) (selected : d154659 p = 0) : d156230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154637 q = 0) : d156208 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154637, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14054 q selected
    | true =>
      simp only [d154637, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154638 q = 0) : d156209 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154638, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154638, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154639 q = 0) : d156210 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154639, d156210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154639, d156210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154640 q = 0) : d156211 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154640, d156211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154640, d156211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154658 q = 0) : d156229 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154658, d156229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154658, d156229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154659 q = 0) : d156230 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154659, d156230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154659, d156230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14059 (p : Pattern) (selected : d154665 p = 0) : d156236 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154643 q = 0) : d156214 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154643, d156214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14053 q selected
    | true =>
      simp only [d154643, d156214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14055 q selected
  have h2 (q : Pattern) (selected : d154644 q = 0) : d156215 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154644, d156215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154644, d156215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154645 q = 0) : d156216 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154645, d156216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154645, d156216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154654 q = 0) : d156225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154654, d156225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14055 q selected
    | true =>
      simp only [d154654, d156225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14057 q selected
  have h5 (q : Pattern) (selected : d154655 q = 0) : d156226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154655, d156226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154655, d156226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154656 q = 0) : d156227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154656, d156227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154656, d156227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154657 q = 0) : d156228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154657, d156228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154657, d156228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154660 q = 0) : d156231 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154660, d156231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14055 q selected
    | true =>
      simp only [d154660, d156231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14058 q selected
  have h9 (q : Pattern) (selected : d154661 q = 0) : d156232 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154661, d156232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154661, d156232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154662 q = 0) : d156233 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154662, d156233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154662, d156233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154663 q = 0) : d156234 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154663, d156234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154663, d156234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154664 q = 0) : d156235 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154664, d156235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154664, d156235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154665 q = 0) : d156236 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154665, d156236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154665, d156236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14060 (p : Pattern) (selected : d154669 p = 0) : d156240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154660 q = 0) : d156231 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154660, d156231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14055 q selected
    | true =>
      simp only [d154660, d156231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14058 q selected
  have h2 (q : Pattern) (selected : d154661 q = 0) : d156232 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154661, d156232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154661, d156232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154662 q = 0) : d156233 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154662, d156233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154662, d156233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154663 q = 0) : d156234 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154663, d156234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154663, d156234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154668 q = 0) : d156239 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154668, d156239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154668, d156239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154669 q = 0) : d156240 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154669, d156240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154669, d156240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14061 (p : Pattern) (selected : d154675 p = 0) : d156246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154666 q = 0) : d156237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154666, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14059 q selected
    | true =>
      simp only [d154666, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154667 q = 0) : d156238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154667, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154667, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154670 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154670, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14060 q selected
    | true =>
      simp only [d154670, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154671 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154671, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154671, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154672 q = 0) : d156243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154672, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154672, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154673 q = 0) : d156244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154673, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154673, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154674 q = 0) : d156245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154674, d156245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154674, d156245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154675 q = 0) : d156246 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154675, d156246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154675, d156246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14062 (p : Pattern) (selected : d154679 p = 0) : d156250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154670 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154670, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14060 q selected
    | true =>
      simp only [d154670, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154671 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154671, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154671, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154676 q = 0) : d156247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154676, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154676, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154677 q = 0) : d156248 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154677, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154677, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154678 q = 0) : d156249 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154678, d156249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154678, d156249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154679 q = 0) : d156250 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154679, d156250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154679, d156250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14063 (p : Pattern) (selected : d154685 p = 0) : d156318 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154544 q = 0) : d156237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14034 q selected
    | true =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154545 q = 0) : d156238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154682 q = 0) : d156315 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154682, d156315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154682, d156315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154683 q = 0) : d156316 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154683, d156316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154683, d156316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154684 q = 0) : d156317 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154684, d156317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154684, d156317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154685 q = 0) : d156318 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154685, d156318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154685, d156318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14064 (p : Pattern) (selected : d154691 p = 0) : d156324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154581 q = 0) : d156274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154581, d156274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14042 q selected
    | true =>
      simp only [d154581, d156274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14043 q selected
  have h2 (q : Pattern) (selected : d154582 q = 0) : d156275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154582, d156275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154582, d156275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154583 q = 0) : d156276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154583, d156276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154583, d156276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154584 q = 0) : d156277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154584, d156277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154584, d156277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154591 q = 0) : d156284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154591, d156284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14044 q selected
    | true =>
      simp only [d154591, d156284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14045 q selected
  have h6 (q : Pattern) (selected : d154592 q = 0) : d156285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154592, d156285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154592, d156285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154593 q = 0) : d156286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154593, d156286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154593, d156286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154620 q = 0) : d156313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154620, d156313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14049 q selected
    | true =>
      simp only [d154620, d156313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14050 q selected
  have h9 (q : Pattern) (selected : d154680 q = 0) : d156251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154680, d156251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14061 q selected
    | true =>
      simp only [d154680, d156251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14062 q selected
  have h10 (q : Pattern) (selected : d154681 q = 0) : d156314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154681, d156314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154681, d156314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154686 q = 0) : d156319 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154686, d156319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14063 q selected
    | true =>
      simp only [d154686, d156319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154687 q = 0) : d156320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154687, d156320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154687, d156320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154688 q = 0) : d156321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154688, d156321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154688, d156321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154689 q = 0) : d156322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154689, d156322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154689, d156322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154690 q = 0) : d156323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154690, d156323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154690, d156323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154691 q = 0) : d156324 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154691, d156324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154691, d156324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro14065 (p : Pattern) (selected : d154692 p = 0) : d156325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154544 q = 0) : d156237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14034 q selected
    | true =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154545 q = 0) : d156238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154550 q = 0) : d156243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154551 q = 0) : d156244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154551, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154551, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154577 q = 0) : d156270 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154577, d156270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154577, d156270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154692 q = 0) : d156325 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154692, d156325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154692, d156325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14066 (p : Pattern) (selected : d154693 p = 0) : d156326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154554 q = 0) : d156247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154555 q = 0) : d156248 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154555, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154555, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154579 q = 0) : d156272 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154579, d156272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154579, d156272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154693 q = 0) : d156326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154693, d156326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154693, d156326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14067 (p : Pattern) (selected : d154698 p = 0) : d156331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154544 q = 0) : d156237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14034 q selected
    | true =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154545 q = 0) : d156238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154550 q = 0) : d156243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154550, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154585 q = 0) : d156278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154585, d156278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154585, d156278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154586 q = 0) : d156279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154586, d156279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154586, d156279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154698 q = 0) : d156331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154698, d156331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154698, d156331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14068 (p : Pattern) (selected : d154699 p = 0) : d156332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154554 q = 0) : d156247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154554, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154588 q = 0) : d156281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154588, d156281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154588, d156281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154589 q = 0) : d156282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154589, d156282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154589, d156282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154699 q = 0) : d156332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154699, d156332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154699, d156332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14069 (p : Pattern) (selected : d154703 p = 0) : d156336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154605 q = 0) : d156298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154605, d156298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14047 q selected
    | true =>
      simp only [d154605, d156298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154606 q = 0) : d156299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154606, d156299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154606, d156299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154610 q = 0) : d156303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154610, d156303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14048 q selected
    | true =>
      simp only [d154610, d156303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154611 q = 0) : d156304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154611, d156304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154611, d156304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154612 q = 0) : d156305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154612, d156305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154612, d156305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154613 q = 0) : d156306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154613, d156306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154613, d156306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154614 q = 0) : d156307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154614, d156307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154614, d156307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154703 q = 0) : d156336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154703, d156336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154703, d156336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14070 (p : Pattern) (selected : d154704 p = 0) : d156337 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154610 q = 0) : d156303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154610, d156303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14048 q selected
    | true =>
      simp only [d154610, d156303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154611 q = 0) : d156304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154611, d156304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154611, d156304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154548 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14035 q selected
    | true =>
      simp only [d154548, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154549 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154549, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154616 q = 0) : d156309 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154616, d156309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154616, d156309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154617 q = 0) : d156310 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154617, d156310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154617, d156310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154618 q = 0) : d156311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154618, d156311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154618, d156311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154704 q = 0) : d156337 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154704, d156337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154704, d156337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14071 (p : Pattern) (selected : d154706 p = 0) : d156259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154666 q = 0) : d156237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154666, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14059 q selected
    | true =>
      simp only [d154666, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154667 q = 0) : d156238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154667, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154667, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154670 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154670, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14060 q selected
    | true =>
      simp only [d154670, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154671 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154671, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154671, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154672 q = 0) : d156243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154672, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154672, d156243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154673 q = 0) : d156244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154673, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154673, d156244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154674 q = 0) : d156245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154674, d156245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154674, d156245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154706 q = 0) : d156259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154706, d156259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154706, d156259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14072 (p : Pattern) (selected : d154707 p = 0) : d156260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154670 q = 0) : d156241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154670, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14060 q selected
    | true =>
      simp only [d154670, d156241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154671 q = 0) : d156242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154671, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154671, d156242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154676 q = 0) : d156247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154676, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154676, d156247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154677 q = 0) : d156248 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154677, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154677, d156248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154678 q = 0) : d156249 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154678, d156249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154678, d156249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154707 q = 0) : d156260 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154707, d156260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154707, d156260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14073 (p : Pattern) (selected : d154710 p = 0) : d156340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154544 q = 0) : d156237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14034 q selected
    | true =>
      simp only [d154544, d156237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154545 q = 0) : d156238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154545, d156238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154682 q = 0) : d156315 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154682, d156315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154682, d156315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154683 q = 0) : d156316 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154683, d156316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154683, d156316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154684 q = 0) : d156317 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154684, d156317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154684, d156317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154710 q = 0) : d156340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154710, d156340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154710, d156340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14074 (p : Pattern) (selected : d154716 p = 0) : d156346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154581 q = 0) : d156274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154581, d156274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14042 q selected
    | true =>
      simp only [d154581, d156274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14043 q selected
  have h2 (q : Pattern) (selected : d154582 q = 0) : d156275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154582, d156275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154582, d156275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154583 q = 0) : d156276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154583, d156276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154583, d156276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154584 q = 0) : d156277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154584, d156277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154584, d156277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154591 q = 0) : d156284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154591, d156284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14044 q selected
    | true =>
      simp only [d154591, d156284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14045 q selected
  have h6 (q : Pattern) (selected : d154592 q = 0) : d156285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154592, d156285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154592, d156285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154593 q = 0) : d156286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154593, d156286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154593, d156286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154620 q = 0) : d156313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154620, d156313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14049 q selected
    | true =>
      simp only [d154620, d156313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14050 q selected
  have h9 (q : Pattern) (selected : d154680 q = 0) : d156251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154680, d156251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14061 q selected
    | true =>
      simp only [d154680, d156251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14062 q selected
  have h10 (q : Pattern) (selected : d154681 q = 0) : d156314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154681, d156314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154681, d156314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154686 q = 0) : d156319 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154686, d156319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14063 q selected
    | true =>
      simp only [d154686, d156319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154687 q = 0) : d156320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154687, d156320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154687, d156320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154688 q = 0) : d156321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154688, d156321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154688, d156321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154689 q = 0) : d156322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154689, d156322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154689, d156322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154690 q = 0) : d156323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154690, d156323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154690, d156323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154694 q = 0) : d156327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154694, d156327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14065 q selected
    | true =>
      simp only [d154694, d156327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14066 q selected
  have h17 (q : Pattern) (selected : d154695 q = 0) : d156328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154695, d156328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154695, d156328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d154696 q = 0) : d156329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154696, d156329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d154696, d156329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d154697 q = 0) : d156330 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154697, d156330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154697, d156330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d154700 q = 0) : d156333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154700, d156333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14067 q selected
    | true =>
      simp only [d154700, d156333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14068 q selected
  have h21 (q : Pattern) (selected : d154701 q = 0) : d156334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154701, d156334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154701, d156334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d154702 q = 0) : d156335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154702, d156335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d154702, d156335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d154705 q = 0) : d156338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154705, d156338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14069 q selected
    | true =>
      simp only [d154705, d156338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14070 q selected
  have h24 (q : Pattern) (selected : d154708 q = 0) : d156261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154708, d156261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14071 q selected
    | true =>
      simp only [d154708, d156261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14072 q selected
  have h25 (q : Pattern) (selected : d154709 q = 0) : d156339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154709, d156339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d154709, d156339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d154711 q = 0) : d156341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154711, d156341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14073 q selected
    | true =>
      simp only [d154711, d156341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d154712 q = 0) : d156342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154712, d156342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d154712, d156342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d154713 q = 0) : d156343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154713, d156343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d154713, d156343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d154714 q = 0) : d156344 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154714, d156344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d154714, d156344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d154715 q = 0) : d156345 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154715, d156345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d154715, d156345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d154716 q = 0) : d156346 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154716, d156346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154716, d156346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro14075 (p : Pattern) (selected : d154728 p = 0) : d156358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154718 q = 0) : d156348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154718, d156348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14050 q selected
    | true =>
      simp only [d154718, d156348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14037 q selected
  have h2 (q : Pattern) (selected : d154719 q = 0) : d156349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154719, d156349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154719, d156349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154720 q = 0) : d156350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154720, d156350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154720, d156350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154721 q = 0) : d156351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154721, d156351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154721, d156351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154722 q = 0) : d156352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154722, d156352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154722, d156352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154723 q = 0) : d156353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154723, d156353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14037 q selected
    | true =>
      simp only [d154723, d156353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154724 q = 0) : d156354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154724, d156354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154724, d156354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154725 q = 0) : d156355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154725, d156355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154725, d156355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154726 q = 0) : d156356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154726, d156356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154726, d156356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154727 q = 0) : d156357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154727, d156357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154727, d156357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154728 q = 0) : d156358 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154728, d156358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154728, d156358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14076 (p : Pattern) (selected : d154734 p = 0) : d156364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154723 q = 0) : d156353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154723, d156353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14037 q selected
    | true =>
      simp only [d154723, d156353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154724 q = 0) : d156354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154724, d156354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154724, d156354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154725 q = 0) : d156355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154725, d156355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154725, d156355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154726 q = 0) : d156356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154726, d156356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154726, d156356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154727 q = 0) : d156357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154727, d156357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154727, d156357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154729 q = 0) : d156359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154729, d156359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14040 q selected
    | true =>
      simp only [d154729, d156359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154730 q = 0) : d156360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154730, d156360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154730, d156360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154731 q = 0) : d156361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154731, d156361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154731, d156361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154732 q = 0) : d156362 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154732, d156362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154732, d156362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154733 q = 0) : d156363 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154733, d156363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154733, d156363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154734 q = 0) : d156364 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154734, d156364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154734, d156364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14077 (p : Pattern) (selected : d154741 p = 0) : d156371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154705 q = 0) : d156338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154705, d156338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14069 q selected
    | true =>
      simp only [d154705, d156338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14070 q selected
  have h2 (q : Pattern) (selected : d154708 q = 0) : d156261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154708, d156261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14071 q selected
    | true =>
      simp only [d154708, d156261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14072 q selected
  have h3 (q : Pattern) (selected : d154709 q = 0) : d156339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154709, d156339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154709, d156339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154711 q = 0) : d156341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154711, d156341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14073 q selected
    | true =>
      simp only [d154711, d156341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154712 q = 0) : d156342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154712, d156342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154712, d156342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154713 q = 0) : d156343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154713, d156343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154713, d156343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154739 q = 0) : d156369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154739, d156369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154739, d156369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154740 q = 0) : d156370 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154740, d156370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154740, d156370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154741 q = 0) : d156371 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154741, d156371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154741, d156371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14078 (p : Pattern) (selected : d154743 p = 0) : d156373 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154729 q = 0) : d156359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154729, d156359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14040 q selected
    | true =>
      simp only [d154729, d156359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154730 q = 0) : d156360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154730, d156360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154730, d156360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154731 q = 0) : d156361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154731, d156361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154731, d156361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154732 q = 0) : d156362 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154732, d156362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154732, d156362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154733 q = 0) : d156363 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154733, d156363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154733, d156363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154743 q = 0) : d156373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154743, d156373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154743, d156373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14079 (p : Pattern) (selected : d154754 p = 0) : d156384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154749 q = 0) : d156379 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154749, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154749, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
  have h2 (q : Pattern) (selected : d154501 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
    | true =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154750 q = 0) : d156380 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154750, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154750, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154502 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154751 q = 0) : d156381 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154751, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154751, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154752 q = 0) : d156382 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154752, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154752, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154753 q = 0) : d156383 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154753, d156383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154753, d156383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154754 q = 0) : d156384 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154754, d156384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154754, d156384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14080 (p : Pattern) (selected : d154760 p = 0) : d156390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154749 q = 0) : d156379 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154749, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154749, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
  have h2 (q : Pattern) (selected : d154501 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
    | true =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154750 q = 0) : d156380 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154750, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154750, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154502 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154751 q = 0) : d156381 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154751, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154751, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154752 q = 0) : d156382 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154752, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154752, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154755 q = 0) : d156385 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154755, d156385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154755, d156385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14027 q selected
  have h8 (q : Pattern) (selected : d154507 q = 0) : d156200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154507, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14027 q selected
    | true =>
      simp only [d154507, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154756 q = 0) : d156386 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154756, d156386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154756, d156386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154508 q = 0) : d156201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154508, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154508, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154757 q = 0) : d156387 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154757, d156387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154757, d156387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154758 q = 0) : d156388 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154758, d156388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154758, d156388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154759 q = 0) : d156389 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154759, d156389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154759, d156389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154760 q = 0) : d156390 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154760, d156390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154760, d156390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro14081 (p : Pattern) (selected : d154773 p = 0) : d156403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154755 q = 0) : d156385 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154755, d156385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154755, d156385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14027 q selected
  have h2 (q : Pattern) (selected : d154507 q = 0) : d156200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154507, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14027 q selected
    | true =>
      simp only [d154507, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154756 q = 0) : d156386 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154756, d156386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154756, d156386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154508 q = 0) : d156201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154508, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154508, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154757 q = 0) : d156387 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154757, d156387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154757, d156387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154758 q = 0) : d156388 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154758, d156388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154758, d156388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154768 q = 0) : d156398 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154768, d156398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154768, d156398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14029 q selected
  have h8 (q : Pattern) (selected : d154515 q = 0) : d156208 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154515, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14029 q selected
    | true =>
      simp only [d154515, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154769 q = 0) : d156399 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154769, d156399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154769, d156399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154516 q = 0) : d156209 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154516, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154516, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154770 q = 0) : d156400 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154770, d156400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154770, d156400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154771 q = 0) : d156401 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154771, d156401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154771, d156401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154772 q = 0) : d156402 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154772, d156402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154772, d156402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154773 q = 0) : d156403 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154773, d156403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154773, d156403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro14082 (p : Pattern) (selected : d154782 p = 0) : d156412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154777 q = 0) : d156407 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154777, d156407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154777, d156407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14031 q selected
  have h2 (q : Pattern) (selected : d154526 q = 0) : d156219 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154526, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14031 q selected
    | true =>
      simp only [d154526, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154778 q = 0) : d156408 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154778, d156408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154778, d156408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154527 q = 0) : d156220 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154527, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154527, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154779 q = 0) : d156409 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154779, d156409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154779, d156409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154780 q = 0) : d156410 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154780, d156410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154780, d156410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154781 q = 0) : d156411 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154781, d156411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154781, d156411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154782 q = 0) : d156412 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154782, d156412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154782, d156412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14083 (p : Pattern) (selected : d154788 p = 0) : d156418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154761 q = 0) : d156391 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154761, d156391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14079 q selected
    | true =>
      simp only [d154761, d156391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14080 q selected
  have h2 (q : Pattern) (selected : d154762 q = 0) : d156392 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154762, d156392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154762, d156392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154763 q = 0) : d156393 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154763, d156393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154763, d156393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154764 q = 0) : d156394 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154764, d156394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14080 q selected
    | true =>
      simp only [d154764, d156394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154765 q = 0) : d156395 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154765, d156395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154765, d156395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154766 q = 0) : d156396 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154766, d156396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154766, d156396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154767 q = 0) : d156397 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154767, d156397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154767, d156397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154774 q = 0) : d156404 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154774, d156404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14080 q selected
    | true =>
      simp only [d154774, d156404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14081 q selected
  have h9 (q : Pattern) (selected : d154775 q = 0) : d156405 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154775, d156405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154775, d156405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154776 q = 0) : d156406 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154776, d156406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154776, d156406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154783 q = 0) : d156413 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154783, d156413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14081 q selected
    | true =>
      simp only [d154783, d156413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14082 q selected
  have h12 (q : Pattern) (selected : d154784 q = 0) : d156414 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154784, d156414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154784, d156414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154785 q = 0) : d156415 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154785, d156415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154785, d156415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154786 q = 0) : d156416 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154786, d156416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154786, d156416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154787 q = 0) : d156417 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154787, d156417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154787, d156417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154788 q = 0) : d156418 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154788, d156418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154788, d156418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14084 (p : Pattern) (selected : d154793 p = 0) : d156423 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154774 q = 0) : d156404 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154774, d156404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14080 q selected
    | true =>
      simp only [d154774, d156404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14081 q selected
  have h2 (q : Pattern) (selected : d154775 q = 0) : d156405 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154775, d156405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154775, d156405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154776 q = 0) : d156406 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154776, d156406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154776, d156406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154783 q = 0) : d156413 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154783, d156413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14081 q selected
    | true =>
      simp only [d154783, d156413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14082 q selected
  have h5 (q : Pattern) (selected : d154784 q = 0) : d156414 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154784, d156414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154784, d156414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154785 q = 0) : d156415 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154785, d156415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154785, d156415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154786 q = 0) : d156416 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154786, d156416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154786, d156416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154791 q = 0) : d156421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154791, d156421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154791, d156421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154792 q = 0) : d156422 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154792, d156422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154792, d156422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154793 q = 0) : d156423 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154793, d156423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154793, d156423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14085 (p : Pattern) (selected : d154799 p = 0) : d156429 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154789 q = 0) : d156419 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154789, d156419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14083 q selected
    | true =>
      simp only [d154789, d156419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154790 q = 0) : d156420 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154790, d156420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154790, d156420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154794 q = 0) : d156424 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154794, d156424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14084 q selected
    | true =>
      simp only [d154794, d156424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154795 q = 0) : d156425 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154795, d156425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154795, d156425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154796 q = 0) : d156426 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154796, d156426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154796, d156426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154797 q = 0) : d156427 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154797, d156427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154797, d156427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154798 q = 0) : d156428 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154798, d156428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154798, d156428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154799 q = 0) : d156429 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154799, d156429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154799, d156429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14086 (p : Pattern) (selected : d154801 p = 0) : d156431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154768 q = 0) : d156398 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154768, d156398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154768, d156398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14029 q selected
  have h2 (q : Pattern) (selected : d154515 q = 0) : d156208 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154515, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14029 q selected
    | true =>
      simp only [d154515, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154769 q = 0) : d156399 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154769, d156399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154769, d156399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154516 q = 0) : d156209 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154516, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154516, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154770 q = 0) : d156400 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154770, d156400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154770, d156400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154771 q = 0) : d156401 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154771, d156401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154771, d156401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154800 q = 0) : d156430 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154800, d156430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154800, d156430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154801 q = 0) : d156431 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154801, d156431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154801, d156431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14087 (p : Pattern) (selected : d154807 p = 0) : d156437 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154802 q = 0) : d156432 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154802, d156432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14081 q selected
    | true =>
      simp only [d154802, d156432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14086 q selected
  have h2 (q : Pattern) (selected : d154803 q = 0) : d156433 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154803, d156433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154803, d156433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154804 q = 0) : d156434 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154804, d156434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154804, d156434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154805 q = 0) : d156435 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154805, d156435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154805, d156435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154806 q = 0) : d156436 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154806, d156436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154806, d156436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154807 q = 0) : d156437 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154807, d156437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154807, d156437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14088 (p : Pattern) (selected : d154813 p = 0) : d156443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154794 q = 0) : d156424 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154794, d156424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14084 q selected
    | true =>
      simp only [d154794, d156424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154795 q = 0) : d156425 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154795, d156425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154795, d156425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154808 q = 0) : d156438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154808, d156438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14087 q selected
    | true =>
      simp only [d154808, d156438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154809 q = 0) : d156439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154809, d156439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154809, d156439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154810 q = 0) : d156440 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154810, d156440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154810, d156440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154811 q = 0) : d156441 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154811, d156441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154811, d156441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154812 q = 0) : d156442 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154812, d156442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154812, d156442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154813 q = 0) : d156443 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154813, d156443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154813, d156443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14089 (p : Pattern) (selected : d154824 p = 0) : d156390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154815 q = 0) : d156379 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154815, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154815, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14051 q selected
  have h2 (q : Pattern) (selected : d154623 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154623, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14051 q selected
    | true =>
      simp only [d154623, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154816 q = 0) : d156380 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154816, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154816, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154624 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154624, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154624, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154817 q = 0) : d156381 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154817, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154817, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154818 q = 0) : d156382 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154818, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154818, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154819 q = 0) : d156385 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154819, d156385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154819, d156385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14052 q selected
  have h8 (q : Pattern) (selected : d154629 q = 0) : d156200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154629, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14052 q selected
    | true =>
      simp only [d154629, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154820 q = 0) : d156386 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154820, d156386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154820, d156386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154630 q = 0) : d156201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154630, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154630, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154821 q = 0) : d156387 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154821, d156387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154821, d156387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154822 q = 0) : d156388 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154822, d156388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154822, d156388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154823 q = 0) : d156389 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154823, d156389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154823, d156389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154824 q = 0) : d156390 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154824, d156390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154824, d156390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro14090 (p : Pattern) (selected : d154830 p = 0) : d156403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154819 q = 0) : d156385 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154819, d156385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154819, d156385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14052 q selected
  have h2 (q : Pattern) (selected : d154629 q = 0) : d156200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154629, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14052 q selected
    | true =>
      simp only [d154629, d156200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154820 q = 0) : d156386 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154820, d156386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154820, d156386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154630 q = 0) : d156201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154630, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154630, d156201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154821 q = 0) : d156387 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154821, d156387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154821, d156387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154822 q = 0) : d156388 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154822, d156388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154822, d156388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154825 q = 0) : d156398 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154825, d156398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154825, d156398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14054 q selected
  have h8 (q : Pattern) (selected : d154637 q = 0) : d156208 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154637, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14054 q selected
    | true =>
      simp only [d154637, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154826 q = 0) : d156399 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154826, d156399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154826, d156399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154638 q = 0) : d156209 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154638, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154638, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154827 q = 0) : d156400 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154827, d156400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154827, d156400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154828 q = 0) : d156401 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154828, d156401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154828, d156401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154829 q = 0) : d156402 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154829, d156402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154829, d156402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154830 q = 0) : d156403 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154830, d156403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154830, d156403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro14091 (p : Pattern) (selected : d154839 p = 0) : d156412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154834 q = 0) : d156407 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154834, d156407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154834, d156407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14056 q selected
  have h2 (q : Pattern) (selected : d154648 q = 0) : d156219 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154648, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14056 q selected
    | true =>
      simp only [d154648, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154835 q = 0) : d156408 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154835, d156408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154835, d156408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154649 q = 0) : d156220 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154649, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154649, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154836 q = 0) : d156409 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154836, d156409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154836, d156409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154837 q = 0) : d156410 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154837, d156410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154837, d156410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154838 q = 0) : d156411 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154838, d156411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154838, d156411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154839 q = 0) : d156412 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154839, d156412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154839, d156412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14092 (p : Pattern) (selected : d154845 p = 0) : d156431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154825 q = 0) : d156398 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154825, d156398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154825, d156398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14054 q selected
  have h2 (q : Pattern) (selected : d154637 q = 0) : d156208 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154637, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14054 q selected
    | true =>
      simp only [d154637, d156208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154826 q = 0) : d156399 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154826, d156399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154826, d156399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154638 q = 0) : d156209 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154638, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154638, d156209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154827 q = 0) : d156400 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154827, d156400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154827, d156400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154828 q = 0) : d156401 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154828, d156401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154828, d156401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154844 q = 0) : d156430 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154844, d156430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154844, d156430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154845 q = 0) : d156431 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154845, d156431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154845, d156431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14093 (p : Pattern) (selected : d154851 p = 0) : d156446 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154831 q = 0) : d156404 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154831, d156404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14089 q selected
    | true =>
      simp only [d154831, d156404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14090 q selected
  have h2 (q : Pattern) (selected : d154832 q = 0) : d156405 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154832, d156405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154832, d156405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154833 q = 0) : d156406 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154833, d156406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154833, d156406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154840 q = 0) : d156413 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154840, d156413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14090 q selected
    | true =>
      simp only [d154840, d156413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14091 q selected
  have h5 (q : Pattern) (selected : d154841 q = 0) : d156414 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154841, d156414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154841, d156414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154842 q = 0) : d156415 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154842, d156415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154842, d156415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154843 q = 0) : d156416 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154843, d156416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154843, d156416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154846 q = 0) : d156432 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154846, d156432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14090 q selected
    | true =>
      simp only [d154846, d156432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14092 q selected
  have h9 (q : Pattern) (selected : d154847 q = 0) : d156433 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154847, d156433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154847, d156433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154848 q = 0) : d156434 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154848, d156434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154848, d156434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154849 q = 0) : d156435 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154849, d156435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154849, d156435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154850 q = 0) : d156445 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154850, d156445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154850, d156445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154851 q = 0) : d156446 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154851, d156446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154851, d156446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14094 (p : Pattern) (selected : d154855 p = 0) : d156437 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154846 q = 0) : d156432 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154846, d156432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14090 q selected
    | true =>
      simp only [d154846, d156432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14092 q selected
  have h2 (q : Pattern) (selected : d154847 q = 0) : d156433 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154847, d156433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154847, d156433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154848 q = 0) : d156434 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154848, d156434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154848, d156434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154849 q = 0) : d156435 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154849, d156435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154849, d156435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154854 q = 0) : d156436 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154854, d156436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154854, d156436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154855 q = 0) : d156437 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154855, d156437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154855, d156437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14095 (p : Pattern) (selected : d154861 p = 0) : d156452 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154852 q = 0) : d156447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154852, d156447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14093 q selected
    | true =>
      simp only [d154852, d156447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154853 q = 0) : d156448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154853, d156448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154853, d156448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154856 q = 0) : d156438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154856, d156438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14094 q selected
    | true =>
      simp only [d154856, d156438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154857 q = 0) : d156439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154857, d156439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154857, d156439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154858 q = 0) : d156449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154858, d156449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154858, d156449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154859 q = 0) : d156450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154859, d156450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154859, d156450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154860 q = 0) : d156451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154860, d156451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154860, d156451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154861 q = 0) : d156452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154861, d156452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154861, d156452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14096 (p : Pattern) (selected : d154865 p = 0) : d156456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154856 q = 0) : d156438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154856, d156438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14094 q selected
    | true =>
      simp only [d154856, d156438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154857 q = 0) : d156439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154857, d156439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154857, d156439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154862 q = 0) : d156453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154862, d156453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154862, d156453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154863 q = 0) : d156454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154863, d156454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154863, d156454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154864 q = 0) : d156455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154864, d156455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154864, d156455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154865 q = 0) : d156456 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154865, d156456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154865, d156456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14097 (p : Pattern) (selected : d154869 p = 0) : d156446 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154774 q = 0) : d156404 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154774, d156404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14080 q selected
    | true =>
      simp only [d154774, d156404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14081 q selected
  have h2 (q : Pattern) (selected : d154775 q = 0) : d156405 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154775, d156405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154775, d156405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154776 q = 0) : d156406 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154776, d156406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154776, d156406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154783 q = 0) : d156413 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154783, d156413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14081 q selected
    | true =>
      simp only [d154783, d156413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14082 q selected
  have h5 (q : Pattern) (selected : d154784 q = 0) : d156414 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154784, d156414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154784, d156414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154785 q = 0) : d156415 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154785, d156415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154785, d156415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154786 q = 0) : d156416 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154786, d156416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154786, d156416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154802 q = 0) : d156432 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154802, d156432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14081 q selected
    | true =>
      simp only [d154802, d156432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14086 q selected
  have h9 (q : Pattern) (selected : d154803 q = 0) : d156433 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154803, d156433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154803, d156433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154804 q = 0) : d156434 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154804, d156434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154804, d156434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154805 q = 0) : d156435 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154805, d156435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154805, d156435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154868 q = 0) : d156445 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154868, d156445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154868, d156445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154869 q = 0) : d156446 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154869, d156446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154869, d156446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14098 (p : Pattern) (selected : d154875 p = 0) : d156462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154870 q = 0) : d156447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154870, d156447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14097 q selected
    | true =>
      simp only [d154870, d156447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154871 q = 0) : d156448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154871, d156448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154871, d156448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154872 q = 0) : d156459 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154872, d156459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154872, d156459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154873 q = 0) : d156460 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154873, d156460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154873, d156460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154874 q = 0) : d156461 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154874, d156461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154874, d156461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154875 q = 0) : d156462 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154875, d156462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154875, d156462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14099 (p : Pattern) (selected : d154881 p = 0) : d156468 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154814 q = 0) : d156444 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154814, d156444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14085 q selected
    | true =>
      simp only [d154814, d156444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14088 q selected
  have h2 (q : Pattern) (selected : d154866 q = 0) : d156457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154866, d156457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14095 q selected
    | true =>
      simp only [d154866, d156457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14096 q selected
  have h3 (q : Pattern) (selected : d154867 q = 0) : d156458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154867, d156458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154867, d156458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154876 q = 0) : d156463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154876, d156463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14098 q selected
    | true =>
      simp only [d154876, d156463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154877 q = 0) : d156464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154877, d156464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154877, d156464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154878 q = 0) : d156465 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154878, d156465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154878, d156465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154879 q = 0) : d156466 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154879, d156466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154879, d156466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154880 q = 0) : d156467 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154880, d156467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154880, d156467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154881 q = 0) : d156468 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154881, d156468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154881, d156468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14100 (p : Pattern) (selected : d154886 p = 0) : d156456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154808 q = 0) : d156438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154808, d156438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14087 q selected
    | true =>
      simp only [d154808, d156438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154809 q = 0) : d156439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154809, d156439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154809, d156439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154883 q = 0) : d156453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154883, d156453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154883, d156453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154884 q = 0) : d156454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154884, d156454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154884, d156454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154885 q = 0) : d156455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154885, d156455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154885, d156455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154886 q = 0) : d156456 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154886, d156456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154886, d156456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14101 (p : Pattern) (selected : d154892 p = 0) : d156475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154887 q = 0) : d156470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154887, d156470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14100 q selected
    | true =>
      simp only [d154887, d156470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154888 q = 0) : d156471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154888, d156471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154888, d156471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154889 q = 0) : d156472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154889, d156472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154889, d156472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154890 q = 0) : d156473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154890, d156473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154890, d156473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154891 q = 0) : d156474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154891, d156474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154891, d156474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154892 q = 0) : d156475 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154892, d156475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154892, d156475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14102 (p : Pattern) (selected : d154898 p = 0) : d156481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154564 q = 0) : d156257 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154564, d156257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154564, d156257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14038 q selected
  have h2 (q : Pattern) (selected : d154565 q = 0) : d156258 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154565, d156258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154565, d156258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154574 q = 0) : d156267 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154574, d156267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14038 q selected
    | true =>
      simp only [d154574, d156267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14041 q selected
  have h4 (q : Pattern) (selected : d154575 q = 0) : d156268 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154575, d156268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154575, d156268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154576 q = 0) : d156269 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154576, d156269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154576, d156269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154717 q = 0) : d156347 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154717, d156347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14064 q selected
    | true =>
      simp only [d154717, d156347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14074 q selected
  have h7 (q : Pattern) (selected : d154735 q = 0) : d156365 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154735, d156365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14075 q selected
    | true =>
      simp only [d154735, d156365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14076 q selected
  have h8 (q : Pattern) (selected : d154736 q = 0) : d156366 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154736, d156366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154736, d156366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154737 q = 0) : d156367 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154737, d156367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154737, d156367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d154738 q = 0) : d156368 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154738, d156368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154738, d156368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154742 q = 0) : d156372 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154742, d156372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154742, d156372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14077 q selected
  have h12 (q : Pattern) (selected : d154744 q = 0) : d156374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154744, d156374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154744, d156374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14078 q selected
  have h13 (q : Pattern) (selected : d154745 q = 0) : d156375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154745, d156375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154745, d156375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154746 q = 0) : d156376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154746, d156376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154746, d156376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d154747 q = 0) : d156377 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154747, d156377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d154747, d156377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d154748 q = 0) : d156378 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154748, d156378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154748, d156378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154882 q = 0) : d156469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154882, d156469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154882, d156469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14099 q selected
  have h18 (q : Pattern) (selected : d154893 q = 0) : d156476 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154893, d156476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154893, d156476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14101 q selected
  have h19 (q : Pattern) (selected : d154894 q = 0) : d156477 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154894, d156477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d154894, d156477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d154895 q = 0) : d156478 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154895, d156478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d154895, d156478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d154896 q = 0) : d156479 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154896, d156479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d154896, d156479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d154897 q = 0) : d156480 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154897, d156480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d154897, d156480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d154898 q = 0) : d156481 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d154898, d156481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154898, d156481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro14103 (p : Pattern) (selected : d154904 p = 0) : d156487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154899 q = 0) : d156482 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d154899, d156482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154899, d156482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14102 q selected
  have h2 (q : Pattern) (selected : d154900 q = 0) : d156483 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d154900, d156483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154900, d156483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154901 q = 0) : d156484 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d154901, d156484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154901, d156484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154902 q = 0) : d156485 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d154902, d156485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154902, d156485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154903 q = 0) : d156486 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d154903, d156486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154903, d156486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154904 q = 0) : d156487 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d154904, d156487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154904, d156487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14104 (p : Pattern) (selected : d154910 p = 0) : d156493 p = 1 := by
  have h0 (q : Pattern) (selected : d153291 q = 0) : d155304 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d153291, d155304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13765 q selected
    | true =>
      simp only [d153291, d155304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13800 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d153584 q = 0) : d155525 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d153584, d155525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153584, d155525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13858 q selected
  have h3 (q : Pattern) (selected : d153585 q = 0) : d155526 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d153585, d155526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153585, d155526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154034 q = 0) : d155851 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d154034, d155851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154034, d155851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13941 q selected
  have h5 (q : Pattern) (selected : d154035 q = 0) : d155852 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d154035, d155852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154035, d155852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154036 q = 0) : d155853 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d154036, d155853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154036, d155853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154495 q = 0) : d156188 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d154495, d156188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154495, d156188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14025 q selected
  have h8 (q : Pattern) (selected : d154496 q = 0) : d156189 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d154496, d156189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154496, d156189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154497 q = 0) : d156190 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d154497, d156190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154497, d156190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154498 q = 0) : d156191 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d154498, d156191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154498, d156191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154905 q = 0) : d156488 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d154905, d156488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154905, d156488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14103 q selected
  have h12 (q : Pattern) (selected : d154906 q = 0) : d156489 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d154906, d156489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154906, d156489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154907 q = 0) : d156490 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d154907, d156490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154907, d156490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154908 q = 0) : d156491 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d154908, d156491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154908, d156491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154909 q = 0) : d156492 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d154909, d156492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154909, d156492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154910 q = 0) : d156493 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d154910, d156493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154910, d156493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro14105 (p : Pattern) (selected : d154916 p = 0) : d156499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154911 q = 0) : d156494 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d154911, d156494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14104 q selected
    | true =>
      simp only [d154911, d156494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154912 q = 0) : d156495 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d154912, d156495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154912, d156495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154913 q = 0) : d156496 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d154913, d156496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154913, d156496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154914 q = 0) : d156497 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d154914, d156497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154914, d156497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154915 q = 0) : d156498 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d154915, d156498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154915, d156498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154916 q = 0) : d156499 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d154916, d156499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154916, d156499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14106 (p : Pattern) (selected : d154922 p = 0) : d156505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154917 q = 0) : d156500 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d154917, d156500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14105 q selected
    | true =>
      simp only [d154917, d156500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154918 q = 0) : d156501 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d154918, d156501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154918, d156501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154919 q = 0) : d156502 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d154919, d156502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154919, d156502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154920 q = 0) : d156503 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d154920, d156503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154920, d156503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154921 q = 0) : d156504 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d154921, d156504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154921, d156504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154922 q = 0) : d156505 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d154922, d156505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154922, d156505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14107 (p : Pattern) (selected : d154928 p = 0) : d156511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154923 q = 0) : d156506 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d154923, d156506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14106 q selected
    | true =>
      simp only [d154923, d156506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154924 q = 0) : d156507 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d154924, d156507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154924, d156507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154925 q = 0) : d156508 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d154925, d156508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154925, d156508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154926 q = 0) : d156509 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d154926, d156509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154926, d156509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154927 q = 0) : d156510 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d154927, d156510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154927, d156510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154928 q = 0) : d156511 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d154928, d156511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154928, d156511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14108 (p : Pattern) (selected : d154934 p = 0) : d156517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154929 q = 0) : d156512 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d154929, d156512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14107 q selected
    | true =>
      simp only [d154929, d156512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154930 q = 0) : d156513 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d154930, d156513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154930, d156513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154931 q = 0) : d156514 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d154931, d156514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154931, d156514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154932 q = 0) : d156515 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d154932, d156515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154932, d156515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154933 q = 0) : d156516 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d154933, d156516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154933, d156516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154934 q = 0) : d156517 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d154934, d156517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154934, d156517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14109 (p : Pattern) (selected : d154940 p = 0) : d156523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154935 q = 0) : d156518 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d154935, d156518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14108 q selected
    | true =>
      simp only [d154935, d156518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154936 q = 0) : d156519 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d154936, d156519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154936, d156519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154937 q = 0) : d156520 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d154937, d156520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154937, d156520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154938 q = 0) : d156521 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d154938, d156521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154938, d156521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154939 q = 0) : d156522 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d154939, d156522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154939, d156522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154940 q = 0) : d156523 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d154940, d156523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154940, d156523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14110 (p : Pattern) (selected : d154946 p = 0) : d156529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154941 q = 0) : d156524 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d154941, d156524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14109 q selected
    | true =>
      simp only [d154941, d156524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154942 q = 0) : d156525 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d154942, d156525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154942, d156525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154943 q = 0) : d156526 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d154943, d156526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154943, d156526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154944 q = 0) : d156527 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d154944, d156527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154944, d156527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154945 q = 0) : d156528 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d154945, d156528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154945, d156528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154946 q = 0) : d156529 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d154946, d156529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154946, d156529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14111 (p : Pattern) (selected : d154952 p = 0) : d156535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154947 q = 0) : d156530 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d154947, d156530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14110 q selected
    | true =>
      simp only [d154947, d156530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154948 q = 0) : d156531 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d154948, d156531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154948, d156531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154949 q = 0) : d156532 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d154949, d156532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154949, d156532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154950 q = 0) : d156533 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d154950, d156533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154950, d156533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154951 q = 0) : d156534 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d154951, d156534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154951, d156534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154952 q = 0) : d156535 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d154952, d156535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154952, d156535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14112 (p : Pattern) (selected : d152983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152982 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d152982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152983 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d152983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14113 (p : Pattern) (selected : d152989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d152984 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14112 q selected
    | true =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152985 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152986 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152987 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152988 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152989 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d152989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14114 (p : Pattern) (selected : d152995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d152990 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14113 q selected
    | true =>
      simp only [d152990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152991 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152992 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152993 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152994 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d152994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152995 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d152995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14115 (p : Pattern) (selected : d153001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d152996 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14114 q selected
    | true =>
      simp only [d152996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152997 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152998 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152999 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153000 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153001 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14116 (p : Pattern) (selected : d153007 p = 1) : d158248 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d152954 q = 1) : d152954 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d152960 q = 1) : d152960 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d152981 q = 1) : d152981 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d153002 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14115 q selected
    | true =>
      simp only [d153002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153003 q = 1) : d158244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153003, d158244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153003, d158244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152877 q = 1) : d152877 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d153004 q = 1) : d158245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153004, d158245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153004, d158245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153005 q = 1) : d158246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153005, d158246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153005, d158246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153006 q = 1) : d158247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153006, d158247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153006, d158247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153007 q = 1) : d158248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153007, d158248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153007, d158248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14117 (p : Pattern) (selected : d153019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d152996 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14114 q selected
    | true =>
      simp only [d152996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152997 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152998 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152999 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153000 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153019 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14118 (p : Pattern) (selected : d153025 p = 1) : d158253 p = 1 := by
  have h0 (q : Pattern) (selected : d152954 q = 1) : d152954 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d152960 q = 1) : d152960 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d152981 q = 1) : d152981 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d153002 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14115 q selected
    | true =>
      simp only [d153002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153003 q = 1) : d158244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153003, d158244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153003, d158244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152877 q = 1) : d152877 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d153004 q = 1) : d158245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153004, d158245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153004, d158245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153005 q = 1) : d158246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153005, d158246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153005, d158246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153006 q = 1) : d158247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153006, d158247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153006, d158247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153012 q = 1) : d153012 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d153016 q = 1) : d153016 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d153018 q = 1) : d153018 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d153020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14117 q selected
    | true =>
      simp only [d153020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d153021 q = 1) : d158249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153021, d158249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153021, d158249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d152884 q = 1) : d152884 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d153022 q = 1) : d158250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153022, d158250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153022, d158250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153023 q = 1) : d158251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153023, d158251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153023, d158251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d153024 q = 1) : d158252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153024, d158252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153024, d158252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153025 q = 1) : d158253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153025, d158253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153025, d158253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro14119 (p : Pattern) (selected : d153034 p = 1) : d158260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153018 q = 1) : d153018 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14117 q selected
    | true =>
      simp only [d153020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153021 q = 1) : d158249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153021, d158249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153021, d158249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152884 q = 1) : d152884 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153022 q = 1) : d158250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153022, d158250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153022, d158250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153032 q = 1) : d158258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153032, d158258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153032, d158258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153033 q = 1) : d158259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153033, d158259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153033, d158259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153034 q = 1) : d158260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153034, d158260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153034, d158260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14120 (p : Pattern) (selected : d153064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153059 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14112 q selected
  have h2 (q : Pattern) (selected : d152984 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14112 q selected
    | true =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153060 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152985 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153061 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153062 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153063 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153064 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14121 (p : Pattern) (selected : d153070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153065 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14120 q selected
    | true =>
      simp only [d153065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153066 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153067 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153068 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153069 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153070 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14122 (p : Pattern) (selected : d153076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14121 q selected
    | true =>
      simp only [d153071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14123 (p : Pattern) (selected : d153082 p = 1) : d158270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153058 q = 1) : d153058 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14122 q selected
    | true =>
      simp only [d153077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153078 q = 1) : d158266 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153078, d158266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153078, d158266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152918 q = 1) : d152918 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153079 q = 1) : d158267 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153079, d158267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153079, d158267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153080 q = 1) : d158268 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153080, d158268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153080, d158268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153081 q = 1) : d158269 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153081, d158269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153081, d158269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153082 q = 1) : d158270 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153082, d158270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153082, d158270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14124 (p : Pattern) (selected : d153088 p = 1) : d158276 p = 1 := by
  have h0 (q : Pattern) (selected : d152948 q = 1) : d152948 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153026 q = 1) : d158254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153026, d158254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14116 q selected
    | true =>
      simp only [d153026, d158254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14118 q selected
  have h2 (q : Pattern) (selected : d153028 q = 1) : d153028 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153029 q = 1) : d158255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153029, d158255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153029, d158255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153030 q = 1) : d158256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153030, d158256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153030, d158256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153031 q = 1) : d158257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153031, d158257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153031, d158257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153035 q = 1) : d158261 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153035, d158261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153035, d158261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14119 q selected
  have h8 (q : Pattern) (selected : d153036 q = 1) : d158262 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153036, d158262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153036, d158262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d153037 q = 1) : d158263 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153037, d158263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153037, d158263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d153038 q = 1) : d158264 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153038, d158264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153038, d158264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d153039 q = 1) : d158265 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153039, d158265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153039, d158265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153083 q = 1) : d158271 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153083, d158271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153083, d158271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14123 q selected
  have h13 (q : Pattern) (selected : d153084 q = 1) : d158272 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153084, d158272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153084, d158272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d153085 q = 1) : d158273 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153085, d158273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153085, d158273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d153086 q = 1) : d158274 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153086, d158274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153086, d158274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d153087 q = 1) : d158275 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153087, d158275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153087, d158275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d153088 q = 1) : d158276 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d153088, d158276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153088, d158276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro14125 (p : Pattern) (selected : d153094 p = 1) : d158282 p = 1 := by
  have h0 (q : Pattern) (selected : d152933 q = 1) : d152933 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153089 q = 1) : d158277 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d153089, d158277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153089, d158277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14124 q selected
  have h3 (q : Pattern) (selected : d153090 q = 1) : d158278 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d153090, d158278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153090, d158278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153091 q = 1) : d158279 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d153091, d158279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153091, d158279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153092 q = 1) : d158280 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d153092, d158280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153092, d158280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153093 q = 1) : d158281 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d153093, d158281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153093, d158281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153094 q = 1) : d158282 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d153094, d158282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153094, d158282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14126 (p : Pattern) (selected : d153151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153150 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153151 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14127 (p : Pattern) (selected : d153157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153152 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14126 q selected
    | true =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153153 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153154 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153155 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152984 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14112 q selected
    | true =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152985 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152986 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152987 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153156 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152988 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d152988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153157 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14128 (p : Pattern) (selected : d153163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153158 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14127 q selected
    | true =>
      simp only [d153158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14113 q selected
  have h2 (q : Pattern) (selected : d153159 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153160 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152990 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14113 q selected
    | true =>
      simp only [d152990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152991 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152992 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153161 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152993 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153162 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153163 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14129 (p : Pattern) (selected : d153169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14128 q selected
    | true =>
      simp only [d153164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152996 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14114 q selected
    | true =>
      simp only [d152996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152997 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153166 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153167 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153168 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153169 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14130 (p : Pattern) (selected : d153181 p = 1) : d158287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153115 q = 1) : d153115 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153121 q = 1) : d153121 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153149 q = 1) : d153149 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d153170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14129 q selected
    | true =>
      simp only [d153170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14115 q selected
  have h5 (q : Pattern) (selected : d153171 q = 1) : d158283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153171, d158283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153171, d158283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153177 q = 1) : d153177 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d153178 q = 1) : d158284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153178, d158284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153178, d158284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153179 q = 1) : d158285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153179, d158285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153179, d158285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153180 q = 1) : d158286 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153180, d158286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153180, d158286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153181 q = 1) : d158287 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153181, d158287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153181, d158287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14131 (p : Pattern) (selected : d153193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14128 q selected
    | true =>
      simp only [d153164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152996 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14114 q selected
    | true =>
      simp only [d152996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152997 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153166 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153167 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153168 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153193 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14132 (p : Pattern) (selected : d153202 p = 1) : d158292 p = 1 := by
  have h0 (q : Pattern) (selected : d153115 q = 1) : d153115 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153121 q = 1) : d153121 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153149 q = 1) : d153149 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14129 q selected
    | true =>
      simp only [d153170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14115 q selected
  have h4 (q : Pattern) (selected : d153171 q = 1) : d158283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153171, d158283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153171, d158283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153177 q = 1) : d153177 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d153178 q = 1) : d158284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153178, d158284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153178, d158284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153179 q = 1) : d158285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153179, d158285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153179, d158285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153180 q = 1) : d158286 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153180, d158286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153180, d158286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153186 q = 1) : d153186 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d153190 q = 1) : d153190 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d153192 q = 1) : d153192 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d153194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14131 q selected
    | true =>
      simp only [d153194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14117 q selected
  have h13 (q : Pattern) (selected : d153195 q = 1) : d158288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153195, d158288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153195, d158288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153198 q = 1) : d153198 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d153199 q = 1) : d158289 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153199, d158289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153199, d158289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153200 q = 1) : d158290 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153200, d158290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153200, d158290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153201 q = 1) : d158291 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153201, d158291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153201, d158291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d153202 q = 1) : d158292 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153202, d158292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153202, d158292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14133 (p : Pattern) (selected : d153211 p = 1) : d158299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153192 q = 1) : d153192 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14131 q selected
    | true =>
      simp only [d153194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14117 q selected
  have h3 (q : Pattern) (selected : d153195 q = 1) : d158288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153195, d158288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153195, d158288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153198 q = 1) : d153198 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153199 q = 1) : d158289 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153199, d158289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153199, d158289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153209 q = 1) : d158297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153209, d158297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153209, d158297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153210 q = 1) : d158298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153210, d158298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153210, d158298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153211 q = 1) : d158299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153211, d158299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153211, d158299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14134 (p : Pattern) (selected : d153248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153243 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14126 q selected
  have h2 (q : Pattern) (selected : d153152 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14126 q selected
    | true =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153244 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153153 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153245 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153246 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153059 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14112 q selected
  have h8 (q : Pattern) (selected : d152984 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14112 q selected
    | true =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153060 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152985 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153061 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153062 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153247 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153063 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153248 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14135 (p : Pattern) (selected : d153254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153249 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14134 q selected
    | true =>
      simp only [d153249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14120 q selected
  have h2 (q : Pattern) (selected : d153250 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153251 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153065 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14120 q selected
    | true =>
      simp only [d153065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153066 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153067 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153252 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153068 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153253 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153254 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14136 (p : Pattern) (selected : d153260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153255 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14135 q selected
    | true =>
      simp only [d153255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153256 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14121 q selected
    | true =>
      simp only [d153071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153257 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153258 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153259 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153260 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14137 (p : Pattern) (selected : d153272 p = 1) : d158309 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153242 q = 1) : d153242 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153261 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14136 q selected
    | true =>
      simp only [d153261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14122 q selected
  have h3 (q : Pattern) (selected : d153262 q = 1) : d158305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153262, d158305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153262, d158305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153268 q = 1) : d153268 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153269 q = 1) : d158306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153269, d158306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153269, d158306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153270 q = 1) : d158307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153270, d158307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153270, d158307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153271 q = 1) : d158308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153271, d158308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153271, d158308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153272 q = 1) : d158309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153272, d158309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153272, d158309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14138 (p : Pattern) (selected : d153284 p = 1) : d158315 p = 1 := by
  have h0 (q : Pattern) (selected : d153109 q = 1) : d153109 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153203 q = 1) : d158293 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153203, d158293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14130 q selected
    | true =>
      simp only [d153203, d158293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14132 q selected
  have h2 (q : Pattern) (selected : d153205 q = 1) : d153205 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153206 q = 1) : d158294 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153206, d158294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153206, d158294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153207 q = 1) : d158295 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153207, d158295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153207, d158295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153208 q = 1) : d158296 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153208, d158296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153208, d158296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153212 q = 1) : d158300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153212, d158300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153212, d158300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14133 q selected
  have h8 (q : Pattern) (selected : d153214 q = 1) : d153214 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d153215 q = 1) : d158301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153215, d158301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153215, d158301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153216 q = 1) : d158302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153216, d158302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153216, d158302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d153217 q = 1) : d158303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153217, d158303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153217, d158303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d153218 q = 1) : d158304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153218, d158304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153218, d158304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153273 q = 1) : d158310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153273, d158310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153273, d158310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14137 q selected
  have h14 (q : Pattern) (selected : d153279 q = 1) : d153279 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d153280 q = 1) : d158311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153280, d158311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153280, d158311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153281 q = 1) : d158312 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153281, d158312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153281, d158312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d153282 q = 1) : d158313 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153282, d158313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153282, d158313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d153283 q = 1) : d158314 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153283, d158314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d153283, d158314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d153284 q = 1) : d158315 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d153284, d158315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153284, d158315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro14139 (p : Pattern) (selected : d153290 p = 1) : d158321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153285 q = 1) : d158316 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d153285, d158316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153285, d158316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14138 q selected
  have h2 (q : Pattern) (selected : d153286 q = 1) : d158317 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d153286, d158317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153286, d158317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153287 q = 1) : d158318 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d153287, d158318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153287, d158318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153288 q = 1) : d158319 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d153288, d158319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153288, d158319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153289 q = 1) : d158320 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d153289, d158320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153289, d158320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153290 q = 1) : d158321 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d153290, d158321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153290, d158321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14140 (p : Pattern) (selected : d153378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d568 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d569 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153377 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153378 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14141 (p : Pattern) (selected : d153385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9655 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6822 q selected
    | true =>
      simp only [d9655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9656 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153384 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153385 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14142 (p : Pattern) (selected : d153391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153379 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14140 q selected
    | true =>
      simp only [d153379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153380 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153382 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153152 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14126 q selected
    | true =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153153 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153154 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153155 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153383 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153386 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14141 q selected
    | true =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153387 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153388 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153389 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d152984 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14112 q selected
    | true =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d152985 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d152986 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d152987 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d152987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153390 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153391 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro14143 (p : Pattern) (selected : d153398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153392 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14142 q selected
    | true =>
      simp only [d153392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14127 q selected
  have h2 (q : Pattern) (selected : d153393 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153394 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153158 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14127 q selected
    | true =>
      simp only [d153158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14113 q selected
  have h5 (q : Pattern) (selected : d153159 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153160 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153395 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153396 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153397 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153398 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14144 (p : Pattern) (selected : d153402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153158 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14127 q selected
    | true =>
      simp only [d153158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14113 q selected
  have h2 (q : Pattern) (selected : d153159 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153160 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153396 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153401 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153402 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14145 (p : Pattern) (selected : d153408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14143 q selected
    | true =>
      simp only [d153399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14144 q selected
    | true =>
      simp only [d153403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153408 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14146 (p : Pattern) (selected : d153412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14144 q selected
    | true =>
      simp only [d153403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153411 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153412 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14147 (p : Pattern) (selected : d153424 p = 1) : d158327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153335 q = 1) : d153335 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153344 q = 1) : d153344 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153376 q = 1) : d153376 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d153413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14145 q selected
    | true =>
      simp only [d153413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14146 q selected
  have h5 (q : Pattern) (selected : d153414 q = 1) : d158323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153414, d158323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153414, d158323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153420 q = 1) : d153420 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d153421 q = 1) : d158324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153421, d158324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153421, d158324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153422 q = 1) : d158325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153422, d158325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153422, d158325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153423 q = 1) : d158326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153423, d158326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153423, d158326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153424 q = 1) : d158327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153424, d158327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153424, d158327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14148 (p : Pattern) (selected : d153438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14143 q selected
    | true =>
      simp only [d153399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14144 q selected
    | true =>
      simp only [d153403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153438 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14149 (p : Pattern) (selected : d153439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14144 q selected
    | true =>
      simp only [d153403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153411 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153439 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14150 (p : Pattern) (selected : d153448 p = 1) : d158332 p = 1 := by
  have h0 (q : Pattern) (selected : d153335 q = 1) : d153335 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153344 q = 1) : d153344 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153376 q = 1) : d153376 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14145 q selected
    | true =>
      simp only [d153413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14146 q selected
  have h4 (q : Pattern) (selected : d153414 q = 1) : d158323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153414, d158323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153414, d158323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153420 q = 1) : d153420 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d153421 q = 1) : d158324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153421, d158324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153421, d158324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153422 q = 1) : d158325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153422, d158325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153422, d158325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153423 q = 1) : d158326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153423, d158326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153423, d158326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153430 q = 1) : d153430 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d153435 q = 1) : d153435 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d153437 q = 1) : d153437 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d153440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14148 q selected
    | true =>
      simp only [d153440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14149 q selected
  have h13 (q : Pattern) (selected : d153441 q = 1) : d158328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153441, d158328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153441, d158328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153444 q = 1) : d153444 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d153445 q = 1) : d158329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153445, d158329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153445, d158329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153446 q = 1) : d158330 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153446, d158330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153446, d158330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153447 q = 1) : d158331 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153447, d158331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153447, d158331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d153448 q = 1) : d158332 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153448, d158332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153448, d158332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14151 (p : Pattern) (selected : d153468 p = 1) : d158339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153437 q = 1) : d153437 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14148 q selected
    | true =>
      simp only [d153440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14149 q selected
  have h3 (q : Pattern) (selected : d153441 q = 1) : d158328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153441, d158328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153441, d158328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153444 q = 1) : d153444 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153445 q = 1) : d158329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153445, d158329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153445, d158329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153466 q = 1) : d158337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153466, d158337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153466, d158337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153467 q = 1) : d158338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153467, d158338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153467, d158338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153468 q = 1) : d158339 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153468, d158339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153468, d158339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14152 (p : Pattern) (selected : d153527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14140 q selected
  have h2 (q : Pattern) (selected : d153379 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14140 q selected
    | true =>
      simp only [d153379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153380 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153519 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153520 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153243 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14126 q selected
  have h8 (q : Pattern) (selected : d153152 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14126 q selected
    | true =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153244 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153153 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153245 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153246 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153521 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153522 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14141 q selected
  have h15 (q : Pattern) (selected : d153386 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14141 q selected
    | true =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153387 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153524 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153525 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153059 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14112 q selected
  have h21 (q : Pattern) (selected : d152984 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14112 q selected
    | true =>
      simp only [d152984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d153060 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d153060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d152985 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d152985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d153061 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d153061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d153062 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d153062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d153526 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d153527 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro14153 (p : Pattern) (selected : d153534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153528 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14152 q selected
    | true =>
      simp only [d153528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14134 q selected
  have h2 (q : Pattern) (selected : d153529 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153530 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153249 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14134 q selected
    | true =>
      simp only [d153249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14120 q selected
  have h5 (q : Pattern) (selected : d153250 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153251 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153531 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153532 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153533 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153534 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14154 (p : Pattern) (selected : d153538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153249 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14134 q selected
    | true =>
      simp only [d153249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14120 q selected
  have h2 (q : Pattern) (selected : d153250 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153251 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153532 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153537 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153538 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14155 (p : Pattern) (selected : d153544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153535 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14153 q selected
    | true =>
      simp only [d153535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153536 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153539 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14154 q selected
    | true =>
      simp only [d153539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153540 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153541 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153542 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153543 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153544 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14156 (p : Pattern) (selected : d153548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153539 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14154 q selected
    | true =>
      simp only [d153539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153540 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153545 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153546 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153547 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14157 (p : Pattern) (selected : d153560 p = 1) : d158349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153516 q = 1) : d153516 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14155 q selected
    | true =>
      simp only [d153549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14156 q selected
  have h3 (q : Pattern) (selected : d153550 q = 1) : d158345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153550, d158345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153550, d158345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153556 q = 1) : d153556 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153557 q = 1) : d158346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153557, d158346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153557, d158346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153558 q = 1) : d158347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153558, d158347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153558, d158347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153559 q = 1) : d158348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153559, d158348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153559, d158348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153560 q = 1) : d158349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153560, d158349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153560, d158349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14158 (p : Pattern) (selected : d153577 p = 1) : d158355 p = 1 := by
  have h0 (q : Pattern) (selected : d153327 q = 1) : d153327 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153449 q = 1) : d158333 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153449, d158333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14147 q selected
    | true =>
      simp only [d153449, d158333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14150 q selected
  have h2 (q : Pattern) (selected : d153462 q = 1) : d153462 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153463 q = 1) : d158334 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153463, d158334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153463, d158334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153464 q = 1) : d158335 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153464, d158335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153464, d158335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153465 q = 1) : d158336 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153465, d158336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153465, d158336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153469 q = 1) : d158340 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153469, d158340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153469, d158340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14151 q selected
  have h8 (q : Pattern) (selected : d153471 q = 1) : d153471 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d153472 q = 1) : d158341 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153472, d158341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153472, d158341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153473 q = 1) : d158342 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153473, d158342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153473, d158342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d153474 q = 1) : d158343 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153474, d158343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153474, d158343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d153475 q = 1) : d158344 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153475, d158344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153475, d158344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153561 q = 1) : d158350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153561, d158350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153561, d158350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14157 q selected
  have h14 (q : Pattern) (selected : d153572 q = 1) : d153572 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d153573 q = 1) : d158351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153573, d158351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153573, d158351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153574 q = 1) : d158352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153574, d158352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153574, d158352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d153575 q = 1) : d158353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153575, d158353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153575, d158353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d153576 q = 1) : d158354 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153576, d158354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d153576, d158354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d153577 q = 1) : d158355 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d153577, d158355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153577, d158355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro14159 (p : Pattern) (selected : d153583 p = 1) : d158361 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153578 q = 1) : d158356 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d153578, d158356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153578, d158356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14158 q selected
  have h2 (q : Pattern) (selected : d153579 q = 1) : d158357 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d153579, d158357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153579, d158357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153580 q = 1) : d158358 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d153580, d158358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153580, d158358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153581 q = 1) : d158359 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d153581, d158359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153581, d158359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153582 q = 1) : d158360 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d153582, d158360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153582, d158360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153583 q = 1) : d158361 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d153583, d158361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153583, d158361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14160 (p : Pattern) (selected : d153725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1237 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro49 q selected
    | true =>
      simp only [d1237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro76 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1238 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d862 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro50 q selected
    | true =>
      simp only [d862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d863 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153724 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153725 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro14161 (p : Pattern) (selected : d153731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1250 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153730 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153731 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro14162 (p : Pattern) (selected : d153738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9902 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6835 q selected
    | true =>
      simp only [d9902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9903 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153737 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153738 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14163 (p : Pattern) (selected : d153744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153726 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14160 q selected
    | true =>
      simp only [d153726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153727 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153728 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153729 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14161 q selected
    | true =>
      simp only [d153732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153734 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153736 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153739 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14162 q selected
    | true =>
      simp only [d153739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153740 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153741 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153742 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d153386 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14141 q selected
    | true =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153387 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153388 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153389 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153743 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153744 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro14164 (p : Pattern) (selected : d153746 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1259 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d1259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1260 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153745 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153746 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro14165 (p : Pattern) (selected : d153753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14161 q selected
    | true =>
      simp only [d153732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153734 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153747 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14164 q selected
    | true =>
      simp only [d153747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153748 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153749 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153750 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153751 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153386 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14141 q selected
    | true =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153387 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153388 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153389 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d153752 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153753 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14166 (p : Pattern) (selected : d153758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d9937 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6822 q selected
    | true =>
      simp only [d9937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d9938 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153757 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153758 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro14167 (p : Pattern) (selected : d153764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153759 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14166 q selected
    | true =>
      simp only [d153759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153760 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153761 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153762 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153763 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153764 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14168 (p : Pattern) (selected : d153770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153747 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14164 q selected
    | true =>
      simp only [d153747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153748 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153749 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153750 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153769 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153770 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14169 (p : Pattern) (selected : d153776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153754 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14163 q selected
    | true =>
      simp only [d153754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14165 q selected
  have h2 (q : Pattern) (selected : d153755 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153756 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153765 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14165 q selected
    | true =>
      simp only [d153765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14167 q selected
  have h5 (q : Pattern) (selected : d153766 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153767 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153768 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153771 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14165 q selected
    | true =>
      simp only [d153771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14168 q selected
  have h9 (q : Pattern) (selected : d153772 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153773 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153774 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153775 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153776 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14170 (p : Pattern) (selected : d153780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153771 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14165 q selected
    | true =>
      simp only [d153771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14168 q selected
  have h2 (q : Pattern) (selected : d153772 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153773 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153774 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153779 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153780 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14171 (p : Pattern) (selected : d153786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153777 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14169 q selected
    | true =>
      simp only [d153777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153778 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153781 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14170 q selected
    | true =>
      simp only [d153781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153782 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14172 (p : Pattern) (selected : d153790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153781 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14170 q selected
    | true =>
      simp only [d153781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153782 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153787 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153788 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153789 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153790 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14173 (p : Pattern) (selected : d153802 p = 1) : d158368 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153672 q = 1) : d153672 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153681 q = 1) : d153681 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153723 q = 1) : d153723 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d153791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14171 q selected
    | true =>
      simp only [d153791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14172 q selected
  have h5 (q : Pattern) (selected : d153792 q = 1) : d158364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153792, d158364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153792, d158364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153798 q = 1) : d153798 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d153799 q = 1) : d158365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153799, d158365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153799, d158365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153800 q = 1) : d158366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153800, d158366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153800, d158366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153801 q = 1) : d158367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153801, d158367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153801, d158367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153802 q = 1) : d158368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153802, d158368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153802, d158368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14174 (p : Pattern) (selected : d153817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153777 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14169 q selected
    | true =>
      simp only [d153777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153778 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153781 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14170 q selected
    | true =>
      simp only [d153781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153782 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153817 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14175 (p : Pattern) (selected : d153818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153781 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14170 q selected
    | true =>
      simp only [d153781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153782 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153787 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153788 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153789 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14176 (p : Pattern) (selected : d153827 p = 1) : d158373 p = 1 := by
  have h0 (q : Pattern) (selected : d153672 q = 1) : d153672 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153681 q = 1) : d153681 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153723 q = 1) : d153723 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14171 q selected
    | true =>
      simp only [d153791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14172 q selected
  have h4 (q : Pattern) (selected : d153792 q = 1) : d158364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153792, d158364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153792, d158364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153798 q = 1) : d153798 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d153799 q = 1) : d158365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153799, d158365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153799, d158365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153800 q = 1) : d158366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153800, d158366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153800, d158366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153801 q = 1) : d158367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153801, d158367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153801, d158367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153808 q = 1) : d153808 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d153813 q = 1) : d153813 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d153816 q = 1) : d153816 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d153819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14174 q selected
    | true =>
      simp only [d153819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14175 q selected
  have h13 (q : Pattern) (selected : d153820 q = 1) : d158369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153820, d158369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153820, d158369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153823 q = 1) : d153823 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d153824 q = 1) : d158370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153824, d158370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153824, d158370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153825 q = 1) : d158371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153825, d158371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153825, d158371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153826 q = 1) : d158372 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153826, d158372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153826, d158372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d153827 q = 1) : d158373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153827, d158373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153827, d158373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14177 (p : Pattern) (selected : d153852 p = 1) : d158380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153816 q = 1) : d153816 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14174 q selected
    | true =>
      simp only [d153819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14175 q selected
  have h3 (q : Pattern) (selected : d153820 q = 1) : d158369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153820, d158369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153820, d158369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153823 q = 1) : d153823 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153824 q = 1) : d158370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153824, d158370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153824, d158370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153850 q = 1) : d158378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153850, d158378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153850, d158378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153851 q = 1) : d158379 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153851, d158379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153851, d158379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153852 q = 1) : d158380 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153852, d158380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153852, d158380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14178 (p : Pattern) (selected : d153952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153938 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14160 q selected
  have h2 (q : Pattern) (selected : d153726 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14160 q selected
    | true =>
      simp only [d153726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153939 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153727 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153940 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153941 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153942 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14161 q selected
  have h8 (q : Pattern) (selected : d153732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14161 q selected
    | true =>
      simp only [d153732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153943 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153944 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153945 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153946 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153947 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14162 q selected
  have h15 (q : Pattern) (selected : d153739 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14162 q selected
    | true =>
      simp only [d153739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153948 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153740 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153949 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153950 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153522 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14141 q selected
  have h21 (q : Pattern) (selected : d153386 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14141 q selected
    | true =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d153523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d153523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d153387 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d153524 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d153524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d153525 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d153525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d153951 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d153952 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro14179 (p : Pattern) (selected : d153959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153942 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14161 q selected
  have h2 (q : Pattern) (selected : d153732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14161 q selected
    | true =>
      simp only [d153732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153943 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153944 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153945 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153953 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14164 q selected
  have h8 (q : Pattern) (selected : d153747 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14164 q selected
    | true =>
      simp only [d153747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153748 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153955 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153956 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153957 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153522 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14141 q selected
  have h15 (q : Pattern) (selected : d153386 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14141 q selected
    | true =>
      simp only [d153386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153387 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153524 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153525 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153958 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d153959 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro14180 (p : Pattern) (selected : d153968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14166 q selected
  have h2 (q : Pattern) (selected : d153759 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14166 q selected
    | true =>
      simp only [d153759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153760 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153965 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153966 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153967 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153968 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14181 (p : Pattern) (selected : d153974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153953 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14164 q selected
  have h2 (q : Pattern) (selected : d153747 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14164 q selected
    | true =>
      simp only [d153747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153748 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153955 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153956 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153974 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14182 (p : Pattern) (selected : d153980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14178 q selected
    | true =>
      simp only [d153960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14179 q selected
  have h2 (q : Pattern) (selected : d153961 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153962 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153969 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14179 q selected
    | true =>
      simp only [d153969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14180 q selected
  have h5 (q : Pattern) (selected : d153970 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153971 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153972 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14179 q selected
    | true =>
      simp only [d153975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14181 q selected
  have h9 (q : Pattern) (selected : d153976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153979 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153980 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14183 (p : Pattern) (selected : d153984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14179 q selected
    | true =>
      simp only [d153975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14181 q selected
  have h2 (q : Pattern) (selected : d153976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153983 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153984 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14184 (p : Pattern) (selected : d153990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14182 q selected
    | true =>
      simp only [d153981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14183 q selected
    | true =>
      simp only [d153985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153987 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153988 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153989 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153990 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14185 (p : Pattern) (selected : d153994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14183 q selected
    | true =>
      simp only [d153985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153991 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153992 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153993 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153994 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14186 (p : Pattern) (selected : d154010 p = 1) : d158390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153937 q = 1) : d153937 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14184 q selected
    | true =>
      simp only [d153995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14185 q selected
  have h3 (q : Pattern) (selected : d153996 q = 1) : d158386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153996, d158386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153996, d158386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154006 q = 1) : d154006 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d154007 q = 1) : d158387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154007, d158387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154007, d158387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154008 q = 1) : d158388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154008, d158388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154008, d158388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154009 q = 1) : d158389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154009, d158389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154009, d158389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154010 q = 1) : d158390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154010, d158390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154010, d158390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14187 (p : Pattern) (selected : d154027 p = 1) : d158396 p = 1 := by
  have h0 (q : Pattern) (selected : d153664 q = 1) : d153664 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153828 q = 1) : d158374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153828, d158374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14173 q selected
    | true =>
      simp only [d153828, d158374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14176 q selected
  have h2 (q : Pattern) (selected : d153846 q = 1) : d153846 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153847 q = 1) : d158375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153847, d158375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153847, d158375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d153848 q = 1) : d158376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153848, d158376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153848, d158376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153849 q = 1) : d158377 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153849, d158377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153849, d158377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153853 q = 1) : d158381 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153853, d158381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153853, d158381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14177 q selected
  have h8 (q : Pattern) (selected : d153855 q = 1) : d153855 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d153856 q = 1) : d158382 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153856, d158382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153856, d158382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153857 q = 1) : d158383 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153857, d158383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153857, d158383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d153858 q = 1) : d158384 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153858, d158384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153858, d158384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d153859 q = 1) : d158385 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153859, d158385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153859, d158385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154011 q = 1) : d158391 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154011, d158391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154011, d158391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14186 q selected
  have h14 (q : Pattern) (selected : d154022 q = 1) : d154022 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d154023 q = 1) : d158392 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154023, d158392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154023, d158392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154024 q = 1) : d158393 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154024, d158393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154024, d158393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d154025 q = 1) : d158394 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154025, d158394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154025, d158394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d154026 q = 1) : d158395 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154026, d158395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d154026, d158395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d154027 q = 1) : d158396 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d154027, d158396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154027, d158396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro14188 (p : Pattern) (selected : d154033 p = 1) : d158402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154028 q = 1) : d158397 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d154028, d158397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154028, d158397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14187 q selected
  have h2 (q : Pattern) (selected : d154029 q = 1) : d158398 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d154029, d158398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154029, d158398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154030 q = 1) : d158399 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d154030, d158399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154030, d158399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154031 q = 1) : d158400 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d154031, d158400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154031, d158400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154032 q = 1) : d158401 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d154032, d158401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154032, d158401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154033 q = 1) : d158402 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d154033, d158402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154033, d158402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14189 (p : Pattern) (selected : d154182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1695 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro106 q selected
    | true =>
      simp only [d1695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro107 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro76 q selected
  have h3 (q : Pattern) (selected : d1697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1705 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro109 q selected
    | true =>
      simp only [d1705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1706 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154181 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154182 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro14190 (p : Pattern) (selected : d154188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1714 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro110 q selected
    | true =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro111 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1715 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h3 (q : Pattern) (selected : d1716 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1720 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1721 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154187 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154188 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro14191 (p : Pattern) (selected : d154195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10184 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6854 q selected
    | true =>
      simp only [d10184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10185 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154194 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154195 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14192 (p : Pattern) (selected : d154201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14189 q selected
    | true =>
      simp only [d154183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154189 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14190 q selected
    | true =>
      simp only [d154189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154190 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154191 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154192 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154193 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154196 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14191 q selected
    | true =>
      simp only [d154196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154197 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154198 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154199 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d154200 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154201 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14193 (p : Pattern) (selected : d154203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1731 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1270 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h3 (q : Pattern) (selected : d1732 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
    | true =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1736 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154202 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154203 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro14194 (p : Pattern) (selected : d154210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154189 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14190 q selected
    | true =>
      simp only [d154189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154190 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154191 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154192 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154204 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14193 q selected
    | true =>
      simp only [d154204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154205 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154206 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154207 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154208 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154196 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14191 q selected
    | true =>
      simp only [d154196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154197 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154198 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154199 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d154209 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d154210 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14195 (p : Pattern) (selected : d154215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d10237 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6854 q selected
    | true =>
      simp only [d10237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d10238 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
    | true =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d1736 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d154214 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154215 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro14196 (p : Pattern) (selected : d154221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154216 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14195 q selected
    | true =>
      simp only [d154216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154218 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154219 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154220 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154221 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14197 (p : Pattern) (selected : d154227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154204 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14193 q selected
    | true =>
      simp only [d154204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154205 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154206 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154207 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154226 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154227 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14198 (p : Pattern) (selected : d154233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154211 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14192 q selected
    | true =>
      simp only [d154211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14194 q selected
  have h2 (q : Pattern) (selected : d154212 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154213 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154222 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14194 q selected
    | true =>
      simp only [d154222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14196 q selected
  have h5 (q : Pattern) (selected : d154223 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154224 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154225 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154228 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14194 q selected
    | true =>
      simp only [d154228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14197 q selected
  have h9 (q : Pattern) (selected : d154229 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154230 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154231 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154232 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154233 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14199 (p : Pattern) (selected : d154237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154228 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14194 q selected
    | true =>
      simp only [d154228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14197 q selected
  have h2 (q : Pattern) (selected : d154229 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154230 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154231 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154236 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154237 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14200 (p : Pattern) (selected : d154243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14198 q selected
    | true =>
      simp only [d154234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154238 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14199 q selected
    | true =>
      simp only [d154238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154239 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154240 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154241 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154242 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14201 (p : Pattern) (selected : d154247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154238 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14199 q selected
    | true =>
      simp only [d154238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154239 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154244 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154245 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154246 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154247 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14202 (p : Pattern) (selected : d154259 p = 1) : d158410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154130 q = 1) : d154130 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d154139 q = 1) : d154139 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d154180 q = 1) : d154180 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d154248 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14200 q selected
    | true =>
      simp only [d154248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14201 q selected
  have h5 (q : Pattern) (selected : d154249 q = 1) : d158406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154249, d158406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154249, d158406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154255 q = 1) : d154255 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d154256 q = 1) : d158407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154256, d158407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154256, d158407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154257 q = 1) : d158408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154257, d158408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154257, d158408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154258 q = 1) : d158409 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154258, d158409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154258, d158409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154259 q = 1) : d158410 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154259, d158410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154259, d158410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14203 (p : Pattern) (selected : d154274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14198 q selected
    | true =>
      simp only [d154234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154238 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14199 q selected
    | true =>
      simp only [d154238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154239 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154240 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154241 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154242 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154274 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14204 (p : Pattern) (selected : d154275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154238 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14199 q selected
    | true =>
      simp only [d154238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154239 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154244 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154245 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154246 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154275 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14205 (p : Pattern) (selected : d154284 p = 1) : d158415 p = 1 := by
  have h0 (q : Pattern) (selected : d154130 q = 1) : d154130 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154139 q = 1) : d154139 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d154180 q = 1) : d154180 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d154248 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14200 q selected
    | true =>
      simp only [d154248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14201 q selected
  have h4 (q : Pattern) (selected : d154249 q = 1) : d158406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154249, d158406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154249, d158406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154255 q = 1) : d154255 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d154256 q = 1) : d158407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154256, d158407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154256, d158407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154257 q = 1) : d158408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154257, d158408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154257, d158408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154258 q = 1) : d158409 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154258, d158409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154258, d158409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154265 q = 1) : d154265 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d154270 q = 1) : d154270 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d154273 q = 1) : d154273 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d154276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14203 q selected
    | true =>
      simp only [d154276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14204 q selected
  have h13 (q : Pattern) (selected : d154277 q = 1) : d158411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154277, d158411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154277, d158411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154280 q = 1) : d154280 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d154281 q = 1) : d158412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154281, d158412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154281, d158412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154282 q = 1) : d158413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154282, d158413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154282, d158413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154283 q = 1) : d158414 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154283, d158414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154283, d158414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d154284 q = 1) : d158415 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154284, d158415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154284, d158415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14206 (p : Pattern) (selected : d154309 p = 1) : d158422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154273 q = 1) : d154273 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d154276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14203 q selected
    | true =>
      simp only [d154276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14204 q selected
  have h3 (q : Pattern) (selected : d154277 q = 1) : d158411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154277, d158411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154277, d158411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154280 q = 1) : d154280 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d154281 q = 1) : d158412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154281, d158412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154281, d158412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154307 q = 1) : d158420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154307, d158420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154307, d158420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154308 q = 1) : d158421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154308, d158421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154308, d158421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154309 q = 1) : d158422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154309, d158422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154309, d158422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14207 (p : Pattern) (selected : d154413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154399 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14189 q selected
  have h2 (q : Pattern) (selected : d154183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14189 q selected
    | true =>
      simp only [d154183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154400 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154401 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154402 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154403 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14190 q selected
  have h8 (q : Pattern) (selected : d154189 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14190 q selected
    | true =>
      simp only [d154189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154404 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154190 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154405 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154406 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154407 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14191 q selected
  have h15 (q : Pattern) (selected : d154196 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14191 q selected
    | true =>
      simp only [d154196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d154409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d154409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154197 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d154410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d154411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d154411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d154412 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d154413 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro14208 (p : Pattern) (selected : d154420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154403 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14190 q selected
  have h2 (q : Pattern) (selected : d154189 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14190 q selected
    | true =>
      simp only [d154189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154404 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154190 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154405 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154406 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154414 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14193 q selected
  have h8 (q : Pattern) (selected : d154204 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14193 q selected
    | true =>
      simp only [d154204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154415 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154205 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154416 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154417 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154418 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14191 q selected
  have h15 (q : Pattern) (selected : d154196 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14191 q selected
    | true =>
      simp only [d154196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d154409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d154409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154197 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d154410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d154411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d154411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d154419 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d154419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d154420 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro14209 (p : Pattern) (selected : d154429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154424 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14195 q selected
  have h2 (q : Pattern) (selected : d154216 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14195 q selected
    | true =>
      simp only [d154216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154425 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154426 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154427 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154428 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154429 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14210 (p : Pattern) (selected : d154435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154414 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14193 q selected
  have h2 (q : Pattern) (selected : d154204 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14193 q selected
    | true =>
      simp only [d154204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154415 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154205 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154416 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154417 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154434 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154435 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14211 (p : Pattern) (selected : d154441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154421 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14207 q selected
    | true =>
      simp only [d154421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14208 q selected
  have h2 (q : Pattern) (selected : d154422 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154423 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154430 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14208 q selected
    | true =>
      simp only [d154430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14209 q selected
  have h5 (q : Pattern) (selected : d154431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154432 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154433 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14208 q selected
    | true =>
      simp only [d154436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14210 q selected
  have h9 (q : Pattern) (selected : d154437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154439 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154440 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154441 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14212 (p : Pattern) (selected : d154445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14208 q selected
    | true =>
      simp only [d154436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14210 q selected
  have h2 (q : Pattern) (selected : d154437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154439 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154444 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154445 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14213 (p : Pattern) (selected : d154451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154442 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14211 q selected
    | true =>
      simp only [d154442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154443 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154446 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14212 q selected
    | true =>
      simp only [d154446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154447 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154448 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154449 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154450 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154451 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14214 (p : Pattern) (selected : d154455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154446 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14212 q selected
    | true =>
      simp only [d154446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154447 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154452 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154453 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154454 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14215 (p : Pattern) (selected : d154471 p = 1) : d158432 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154398 q = 1) : d154398 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d154456 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14213 q selected
    | true =>
      simp only [d154456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14214 q selected
  have h3 (q : Pattern) (selected : d154457 q = 1) : d158428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154457, d158428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154457, d158428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154467 q = 1) : d154467 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d154468 q = 1) : d158429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154468, d158429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154468, d158429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154469 q = 1) : d158430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154469, d158430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154469, d158430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154470 q = 1) : d158431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154470, d158431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154470, d158431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154471 q = 1) : d158432 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154471, d158432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154471, d158432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14216 (p : Pattern) (selected : d154488 p = 1) : d158438 p = 1 := by
  have h0 (q : Pattern) (selected : d154122 q = 1) : d154122 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154285 q = 1) : d158416 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154285, d158416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14202 q selected
    | true =>
      simp only [d154285, d158416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14205 q selected
  have h2 (q : Pattern) (selected : d154303 q = 1) : d154303 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d154304 q = 1) : d158417 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154304, d158417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154304, d158417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d154305 q = 1) : d158418 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154305, d158418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154305, d158418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154306 q = 1) : d158419 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154306, d158419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154306, d158419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154310 q = 1) : d158423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154310, d158423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154310, d158423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14206 q selected
  have h8 (q : Pattern) (selected : d154312 q = 1) : d154312 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d154313 q = 1) : d158424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154313, d158424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154313, d158424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154314 q = 1) : d158425 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154314, d158425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154314, d158425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d154315 q = 1) : d158426 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154315, d158426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154315, d158426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d154316 q = 1) : d158427 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154316, d158427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154316, d158427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154472 q = 1) : d158433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154472, d158433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154472, d158433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14215 q selected
  have h14 (q : Pattern) (selected : d154483 q = 1) : d154483 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d154484 q = 1) : d158434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154484, d158434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154484, d158434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154485 q = 1) : d158435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154485, d158435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154485, d158435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d154486 q = 1) : d158436 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154486, d158436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154486, d158436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d154487 q = 1) : d158437 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154487, d158437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d154487, d158437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d154488 q = 1) : d158438 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d154488, d158438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154488, d158438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro14217 (p : Pattern) (selected : d154494 p = 1) : d158444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154489 q = 1) : d158439 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d154489, d158439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154489, d158439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14216 q selected
  have h2 (q : Pattern) (selected : d154490 q = 1) : d158440 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d154490, d158440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154490, d158440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154491 q = 1) : d158441 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d154491, d158441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154491, d158441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154492 q = 1) : d158442 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d154492, d158442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154492, d158442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154493 q = 1) : d158443 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d154493, d158443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154493, d158443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154494 q = 1) : d158444 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d154494, d158444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154494, d158444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14218 (p : Pattern) (selected : d154622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2170 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro141 q selected
    | true =>
      simp only [d2170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro142 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2174 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro143 q selected
  have h3 (q : Pattern) (selected : d2175 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154621 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d154622 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro14219 (p : Pattern) (selected : d154628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2186 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro144 q selected
    | true =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro145 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h3 (q : Pattern) (selected : d2191 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2195 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro147 q selected
    | true =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2196 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154627 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154628 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro14220 (p : Pattern) (selected : d154634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14218 q selected
    | true =>
      simp only [d154623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154625 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154626 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154629 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14219 q selected
    | true =>
      simp only [d154629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154630 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154631 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154632 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154633 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154634 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14221 (p : Pattern) (selected : d154636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2207 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro149 q selected
    | true =>
      simp only [d2207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro150 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h3 (q : Pattern) (selected : d2210 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
    | true =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154635 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154636 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro14222 (p : Pattern) (selected : d154642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154629 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14219 q selected
    | true =>
      simp only [d154629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154630 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154631 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154632 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154637 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14221 q selected
    | true =>
      simp only [d154637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154638 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154639 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154640 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154641 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154642 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14223 (p : Pattern) (selected : d154647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10476 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
  have h2 (q : Pattern) (selected : d10477 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
    | true =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154646 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154647 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14224 (p : Pattern) (selected : d154653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154648 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14223 q selected
    | true =>
      simp only [d154648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154649 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154650 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154651 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154652 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154653 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14225 (p : Pattern) (selected : d154659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154637 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14221 q selected
    | true =>
      simp only [d154637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154638 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154639 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154640 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154658 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154659 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14226 (p : Pattern) (selected : d154665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14220 q selected
    | true =>
      simp only [d154643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14222 q selected
  have h2 (q : Pattern) (selected : d154644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154654 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14222 q selected
    | true =>
      simp only [d154654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14224 q selected
  have h5 (q : Pattern) (selected : d154655 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154656 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154657 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154660 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14222 q selected
    | true =>
      simp only [d154660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14225 q selected
  have h9 (q : Pattern) (selected : d154661 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154662 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154663 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154664 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154665 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14227 (p : Pattern) (selected : d154669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154660 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14222 q selected
    | true =>
      simp only [d154660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14225 q selected
  have h2 (q : Pattern) (selected : d154661 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154662 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154663 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154668 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154669 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14228 (p : Pattern) (selected : d154675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14226 q selected
    | true =>
      simp only [d154666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154667 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154670 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14227 q selected
    | true =>
      simp only [d154670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154671 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154672 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154673 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154674 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154675 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14229 (p : Pattern) (selected : d154679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154670 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14227 q selected
    | true =>
      simp only [d154670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154671 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154676 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154677 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154678 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154679 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14230 (p : Pattern) (selected : d154691 p = 1) : d158453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154584 q = 1) : d154584 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d154593 q = 1) : d154593 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d154620 q = 1) : d154620 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d154680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14228 q selected
    | true =>
      simp only [d154680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14229 q selected
  have h5 (q : Pattern) (selected : d154681 q = 1) : d158449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154681, d158449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154681, d158449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154687 q = 1) : d154687 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d154688 q = 1) : d158450 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154688, d158450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154688, d158450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154689 q = 1) : d158451 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154689, d158451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154689, d158451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154690 q = 1) : d158452 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154690, d158452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154690, d158452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154691 q = 1) : d158453 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154691, d158453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154691, d158453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14231 (p : Pattern) (selected : d154706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14226 q selected
    | true =>
      simp only [d154666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154667 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154670 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14227 q selected
    | true =>
      simp only [d154670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154671 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154672 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154673 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154674 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154706 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14232 (p : Pattern) (selected : d154707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154670 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14227 q selected
    | true =>
      simp only [d154670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154671 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154676 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154677 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154678 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154707 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14233 (p : Pattern) (selected : d154716 p = 1) : d158458 p = 1 := by
  have h0 (q : Pattern) (selected : d154584 q = 1) : d154584 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154593 q = 1) : d154593 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d154620 q = 1) : d154620 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d154680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14228 q selected
    | true =>
      simp only [d154680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14229 q selected
  have h4 (q : Pattern) (selected : d154681 q = 1) : d158449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154681, d158449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154681, d158449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154687 q = 1) : d154687 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d154688 q = 1) : d158450 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154688, d158450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154688, d158450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154689 q = 1) : d158451 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154689, d158451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154689, d158451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154690 q = 1) : d158452 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154690, d158452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154690, d158452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154697 q = 1) : d154697 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d154702 q = 1) : d154702 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d154705 q = 1) : d154705 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d154708 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14231 q selected
    | true =>
      simp only [d154708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14232 q selected
  have h13 (q : Pattern) (selected : d154709 q = 1) : d158454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154709, d158454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154709, d158454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154712 q = 1) : d154712 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d154713 q = 1) : d158455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154713, d158455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154713, d158455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154714 q = 1) : d158456 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154714, d158456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154714, d158456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154715 q = 1) : d158457 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154715, d158457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154715, d158457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d154716 q = 1) : d158458 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154716, d158458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154716, d158458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14234 (p : Pattern) (selected : d154741 p = 1) : d158465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154705 q = 1) : d154705 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d154708 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14231 q selected
    | true =>
      simp only [d154708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14232 q selected
  have h3 (q : Pattern) (selected : d154709 q = 1) : d158454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154709, d158454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154709, d158454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154712 q = 1) : d154712 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d154713 q = 1) : d158455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154713, d158455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154713, d158455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154739 q = 1) : d158463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154739, d158463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154739, d158463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154740 q = 1) : d158464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154740, d158464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154740, d158464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154741 q = 1) : d158465 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154741, d158465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154741, d158465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14235 (p : Pattern) (selected : d154824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154815 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14218 q selected
  have h2 (q : Pattern) (selected : d154623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14218 q selected
    | true =>
      simp only [d154623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154816 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154817 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154818 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154819 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14219 q selected
  have h8 (q : Pattern) (selected : d154629 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14219 q selected
    | true =>
      simp only [d154629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154820 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154630 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154821 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154822 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154823 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154824 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro14236 (p : Pattern) (selected : d154830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154819 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14219 q selected
  have h2 (q : Pattern) (selected : d154629 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14219 q selected
    | true =>
      simp only [d154629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154820 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154630 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154821 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154822 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14221 q selected
  have h8 (q : Pattern) (selected : d154637 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14221 q selected
    | true =>
      simp only [d154637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154638 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154827 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d154828 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154829 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154830 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro14237 (p : Pattern) (selected : d154839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14223 q selected
  have h2 (q : Pattern) (selected : d154648 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14223 q selected
    | true =>
      simp only [d154648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154649 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154839 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14238 (p : Pattern) (selected : d154845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14221 q selected
  have h2 (q : Pattern) (selected : d154637 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14221 q selected
    | true =>
      simp only [d154637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154638 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154827 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154828 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154844 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154845 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14239 (p : Pattern) (selected : d154851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154831 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14235 q selected
    | true =>
      simp only [d154831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14236 q selected
  have h2 (q : Pattern) (selected : d154832 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154833 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154840 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14236 q selected
    | true =>
      simp only [d154840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14237 q selected
  have h5 (q : Pattern) (selected : d154841 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154842 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154843 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154846 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14236 q selected
    | true =>
      simp only [d154846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14238 q selected
  have h9 (q : Pattern) (selected : d154847 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154848 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154849 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154850 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154851 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14240 (p : Pattern) (selected : d154855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154846 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14236 q selected
    | true =>
      simp only [d154846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14238 q selected
  have h2 (q : Pattern) (selected : d154847 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154848 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154849 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154854 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154855 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14241 (p : Pattern) (selected : d154861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154852 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14239 q selected
    | true =>
      simp only [d154852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154853 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14240 q selected
    | true =>
      simp only [d154856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154858 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154859 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154860 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154861 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14242 (p : Pattern) (selected : d154865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14240 q selected
    | true =>
      simp only [d154856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154862 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154863 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154865 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14243 (p : Pattern) (selected : d154881 p = 1) : d158475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154814 q = 1) : d154814 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d154866 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14241 q selected
    | true =>
      simp only [d154866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14242 q selected
  have h3 (q : Pattern) (selected : d154867 q = 1) : d158471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154867, d158471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154867, d158471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154877 q = 1) : d154877 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d154878 q = 1) : d158472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154878, d158472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154878, d158472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154879 q = 1) : d158473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154879, d158473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154879, d158473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154880 q = 1) : d158474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154880, d158474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154880, d158474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154881 q = 1) : d158475 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154881, d158475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154881, d158475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14244 (p : Pattern) (selected : d154898 p = 1) : d158481 p = 1 := by
  have h0 (q : Pattern) (selected : d154576 q = 1) : d154576 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154717 q = 1) : d158459 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154717, d158459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14230 q selected
    | true =>
      simp only [d154717, d158459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14233 q selected
  have h2 (q : Pattern) (selected : d154735 q = 1) : d154735 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d154736 q = 1) : d158460 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154736, d158460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154736, d158460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d154737 q = 1) : d158461 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154737, d158461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154737, d158461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154738 q = 1) : d158462 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154738, d158462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154738, d158462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154742 q = 1) : d158466 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154742, d158466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154742, d158466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14234 q selected
  have h8 (q : Pattern) (selected : d154744 q = 1) : d154744 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d154745 q = 1) : d158467 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154745, d158467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154745, d158467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154746 q = 1) : d158468 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154746, d158468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154746, d158468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d154747 q = 1) : d158469 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154747, d158469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154747, d158469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d154748 q = 1) : d158470 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154748, d158470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154748, d158470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154882 q = 1) : d158476 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154882, d158476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154882, d158476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14243 q selected
  have h14 (q : Pattern) (selected : d154893 q = 1) : d154893 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d154894 q = 1) : d158477 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154894, d158477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154894, d158477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154895 q = 1) : d158478 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154895, d158478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154895, d158478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d154896 q = 1) : d158479 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154896, d158479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154896, d158479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d154897 q = 1) : d158480 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154897, d158480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d154897, d158480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d154898 q = 1) : d158481 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d154898, d158481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154898, d158481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro14245 (p : Pattern) (selected : d154904 p = 1) : d158487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154899 q = 1) : d158482 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d154899, d158482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154899, d158482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14244 q selected
  have h2 (q : Pattern) (selected : d154900 q = 1) : d158483 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d154900, d158483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154900, d158483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154901 q = 1) : d158484 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d154901, d158484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154901, d158484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154902 q = 1) : d158485 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d154902, d158485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154902, d158485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154903 q = 1) : d158486 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d154903, d158486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154903, d158486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154904 q = 1) : d158487 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d154904, d158487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154904, d158487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14246 (p : Pattern) (selected : d154910 p = 1) : d158493 p = 1 := by
  have h0 (q : Pattern) (selected : d153291 q = 1) : d158322 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d153291, d158322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14125 q selected
    | true =>
      simp only [d153291, d158322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14139 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153584 q = 1) : d158362 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d153584, d158362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153584, d158362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14159 q selected
  have h3 (q : Pattern) (selected : d153585 q = 1) : d158363 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d153585, d158363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153585, d158363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154034 q = 1) : d158403 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d154034, d158403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154034, d158403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14188 q selected
  have h5 (q : Pattern) (selected : d154035 q = 1) : d158404 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d154035, d158404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154035, d158404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154036 q = 1) : d158405 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d154036, d158405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154036, d158405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154495 q = 1) : d158445 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d154495, d158445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154495, d158445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14217 q selected
  have h8 (q : Pattern) (selected : d154496 q = 1) : d158446 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d154496, d158446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154496, d158446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154497 q = 1) : d158447 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d154497, d158447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154497, d158447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154498 q = 1) : d158448 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d154498, d158448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154498, d158448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154905 q = 1) : d158488 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d154905, d158488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154905, d158488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14245 q selected
  have h12 (q : Pattern) (selected : d154906 q = 1) : d158489 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d154906, d158489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154906, d158489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154907 q = 1) : d158490 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d154907, d158490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154907, d158490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154908 q = 1) : d158491 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d154908, d158491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154908, d158491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154909 q = 1) : d158492 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d154909, d158492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154909, d158492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154910 q = 1) : d158493 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d154910, d158493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154910, d158493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro14247 (p : Pattern) (selected : d154916 p = 1) : d158499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154911 q = 1) : d158494 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d154911, d158494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14246 q selected
    | true =>
      simp only [d154911, d158494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154912 q = 1) : d158495 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d154912, d158495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154912, d158495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154913 q = 1) : d158496 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d154913, d158496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154913, d158496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154914 q = 1) : d158497 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d154914, d158497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154914, d158497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154915 q = 1) : d158498 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d154915, d158498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154915, d158498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154916 q = 1) : d158499 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d154916, d158499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154916, d158499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14248 (p : Pattern) (selected : d154922 p = 1) : d158505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154917 q = 1) : d158500 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d154917, d158500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14247 q selected
    | true =>
      simp only [d154917, d158500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154918 q = 1) : d158501 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d154918, d158501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154918, d158501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154919 q = 1) : d158502 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d154919, d158502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154919, d158502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154920 q = 1) : d158503 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d154920, d158503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154920, d158503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154921 q = 1) : d158504 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d154921, d158504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154921, d158504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154922 q = 1) : d158505 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d154922, d158505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154922, d158505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14249 (p : Pattern) (selected : d154928 p = 1) : d158511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154923 q = 1) : d158506 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d154923, d158506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14248 q selected
    | true =>
      simp only [d154923, d158506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154924 q = 1) : d158507 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d154924, d158507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154924, d158507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154925 q = 1) : d158508 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d154925, d158508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154925, d158508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154926 q = 1) : d158509 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d154926, d158509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154926, d158509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154927 q = 1) : d158510 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d154927, d158510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154927, d158510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154928 q = 1) : d158511 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d154928, d158511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154928, d158511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
